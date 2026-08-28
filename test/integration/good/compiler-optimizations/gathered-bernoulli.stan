data {
  int<lower=1> N;
  int<lower=1> I;
  int<lower=1> J;
  array[N] int<lower=1, upper=I> ii;
  array[N] int<lower=1, upper=J> jj;
  array[N] int<lower=0, upper=1> y;
}
parameters {
  vector[I] alpha;
  vector[I] beta;
  vector[J] theta;
  vector[N] gamma;
}
model {
  // gathered: the exact 2PL predictor alpha[ii] .* (theta[jj] - beta[ii])
  // (fires at --O1 and up, reverse-mode instantiation only)
  y ~ bernoulli_logit(alpha[ii] .* (theta[jj] - beta[ii]));
  // gathered: the explicit lpmf form (drops constant terms)
  target += bernoulli_logit_lpmf(y | alpha[ii] .* (theta[jj] - beta[ii]));
  // not gathered: elementwise over non-indexed containers
  y ~ bernoulli_logit(alpha .* (theta - beta));
  // not gathered: the gathered eltwise chain feeds normal_lpdf, not
  // bernoulli_logit_lpmf
  gamma ~ normal(alpha[ii] .* (theta[jj] - beta[ii]), 1.0);
  // not gathered: three-term gather (four leaves in the eltwise tree)
  y ~ bernoulli_logit(alpha[ii] .* beta[ii] .* (theta[jj] - beta[ii]));
  // not gathered: alpha and beta gathered through different index vectors
  y ~ bernoulli_logit(alpha[ii] .* (theta[jj] - beta[jj]));
}
