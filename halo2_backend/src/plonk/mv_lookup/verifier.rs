use std::iter;

use super::super::{ChallengeBeta, ChallengeTheta, ChallengeX};
use super::Argument;
use crate::{
    arithmetic::CurveAffine,
    plonk::circuit::{ExpressionBack, QueryBack, VarBack},
    plonk::{Error, VerifyingKey},
    poly::{commitment::MSM, VerifierQuery},
    transcript::{EncodedChallenge, TranscriptRead},
};
use halo2_middleware::circuit::Any;
use halo2_middleware::ff::{BatchInvert, Field};
use halo2_middleware::poly::Rotation;

pub struct PreparedCommitments<C: CurveAffine> {
    m_commitment: C,
}

pub struct Committed<C: CurveAffine> {
    prepared: PreparedCommitments<C>,
    phi_commitment: C,
}

pub struct Evaluated<C: CurveAffine> {
    committed: Committed<C>,
    phi_eval: C::Scalar,
    phi_next_eval: C::Scalar,
    m_eval: C::Scalar,
}

pub(in crate::plonk) fn lookup_read_prepared_commitments<
    C: CurveAffine,
    E: EncodedChallenge<C>,
    T: TranscriptRead<C, E>,
>(
    transcript: &mut T,
) -> Result<PreparedCommitments<C>, Error> {
    let m_commitment = transcript.read_point()?;

    Ok(PreparedCommitments { m_commitment })
}


impl<C: CurveAffine> PreparedCommitments<C> {
    pub(in crate::plonk) fn read_grand_sum_commitment<
        E: EncodedChallenge<C>,
        T: TranscriptRead<C, E>,
    >(
        self,
        transcript: &mut T,
    ) -> Result<Committed<C>, Error> {
        let phi_commitment = transcript.read_point()?;

        Ok(Committed {
            prepared: self,
            phi_commitment,
        })
    }
}

impl<C: CurveAffine> Committed<C> {
    pub(crate) fn evaluate<E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
        self,
        transcript: &mut T,
    ) -> Result<Evaluated<C>, Error> {
        let phi_eval = transcript.read_scalar()?;
        let phi_next_eval = transcript.read_scalar()?;
        let m_eval = transcript.read_scalar()?;

        Ok(Evaluated {
            committed: self,
            phi_eval,
            phi_next_eval,
            m_eval,
        })
    }
}

impl<C: CurveAffine> Evaluated<C> {
    pub(in crate::plonk) fn expressions<'a>(
        &'a self,
        l_0: C::Scalar,
        l_last: C::Scalar,
        l_blind: C::Scalar,
        argument: &'a Argument<C::Scalar>,
        theta: ChallengeTheta<C>,
        beta: ChallengeBeta<C>,
        advice_evals: &[C::Scalar],
        fixed_evals: &[C::Scalar],
        instance_evals: &[C::Scalar],
        challenges: &[C::Scalar],
    ) -> impl Iterator<Item = C::Scalar> + 'a {
        let active_rows = C::Scalar::ONE - (l_last + l_blind);

        /*
            φ_i(X) = f_i(X) + α
            τ(X) = t(X) + α
            LHS = τ(X) * Π(φ_i(X)) * (ϕ(gX) - ϕ(X))
            RHS = τ(X) * Π(φ_i(X)) * (∑ 1/(φ_i(X)) - m(X) / τ(X))))
        */

        let grand_sum_expression = || {
            let compress_expressions = |expressions: &[ExpressionBack<C::Scalar>]| {
                expressions
                    .iter()
                    .map(|expression| {
                         expression.evaluate(
                            &|scalar| scalar,
                            &|var| match var {
                                VarBack::Challenge(challenge) => challenges[challenge.index],
                                VarBack::Query(QueryBack {
                                    index, column_type, ..
                                }) => match column_type {
                                    Any::Fixed => fixed_evals[index],
                                    Any::Advice => advice_evals[index],
                                    Any::Instance => instance_evals[index],
                                },
                            },
                            &|a| -a,
                            &|a, b| a + b,
                            &|a, b| a * b,
                        )
                    })
                    .fold(C::Scalar::ZERO, |acc, eval| acc * &*theta + &eval)
            };

            // φ_i(X) = f_i(X) + α
            #[cfg(feature = "mv-lookup")]
            let mut f_evals = argument
                .inputs_expressions
                .iter()
                .map(|input_expressions| compress_expressions(input_expressions) + *beta)
                .collect::<Vec<_>>();
            #[cfg(not(feature = "mv-lookup"))]
            let mut f_evals: Vec<_> = argument
                .input_expressions
                .iter()
                .map(|input_expressions| compress_expressions(input_expressions) + *beta)
                .collect();


            let t_eval = compress_expressions(&argument.table_expressions);

            let tau = t_eval + *beta;
            // Π(φ_i(X))
            let prod_fi = f_evals.iter().fold(C::Scalar::ONE, |acc, eval| acc * eval);
            // ∑ 1/(φ_i(X))
            let sum_inv_fi = {
                f_evals.batch_invert();
                f_evals.iter().fold(C::Scalar::ZERO, |acc, eval| acc + eval)
            };

            // LHS = τ(X) * Π(φ_i(X)) * (ϕ(gX) - ϕ(X))
            let lhs = tau * prod_fi * (self.phi_next_eval - self.phi_eval);

            // RHS = τ(X) * Π(φ_i(X)) * (∑ 1/(φ_i(X)) - m(X) / τ(X))))
            let rhs = { tau * prod_fi * (sum_inv_fi - self.m_eval * tau.invert().unwrap()) };

            (lhs - rhs) * active_rows
        };

        std::iter::empty()
            .chain(
                // phi[0] = 0
                Some(l_0 * self.phi_eval),
            )
            .chain(
                // phi[u] = 0
                Some(l_last * self.phi_eval),
            )
            .chain(
                // l_last(X) * (z(X)^2 - z(X)) = 0
                Some(grand_sum_expression()),
            )
    }

    pub(in crate::plonk) fn queries<'r, M: MSM<C> + 'r>(
        &'r self,
        vk: &'r VerifyingKey<C>,
        x: ChallengeX<C>,
    ) -> impl Iterator<Item = VerifierQuery<'r, C, M>> + Clone {
        let x_next = vk.domain.rotate_omega(*x, Rotation::next());

        iter::empty()
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.phi_commitment,
                *x,
                self.phi_eval,
            )))
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.phi_commitment,
                x_next,
                self.phi_next_eval,
            )))
            .chain(Some(VerifierQuery::new_commitment(
                &self.committed.prepared.m_commitment,
                *x,
                self.m_eval,
            )))
    }
}
