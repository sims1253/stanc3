data {
  int<lower=1> N;
  int<lower=1> G1;
  int<lower=1> G2;
  array[N] int<lower=1, upper=G1> idx1;
  array[N] int<lower=1, upper=G2> idx2;
  vector<lower=0, upper=1>[N] x1;
  vector<lower=0, upper=1>[N] x2;
  vector[N] x3;
  array[N] int<lower=0, upper=1> y;
  vector[N] y2;
}
parameters {
  vector[G1] a;
  vector[G2] b;
  vector[4] beta;
  real<lower=0> sigma;
  real mu_a;
}
transformed parameters {
  vector[N] y_hat;
  vector[N] y_hat2;
  vector[N] y_neg_read;
  vector[N] y_neg_print;
  vector[N] y_neg_gq;
  vector[N] y_neg_partial;
  vector[N] y_neg_nonlin;
  vector[N] y_neg_bound;
  vector[N] y_neg_otherhead;
  vector[N] y_neg_nolike;
  vector[N] y_neg_gather_slope;
  real y_neg_scalar;
  // fires at --O1 and up (reverse-mode instantiation only): the election88
  // shape — leading coefficient-slot intercept, slot*data slopes, a
  // (slot*data)*data product and gathered coefficient reads; the loop
  // becomes the gathered_additive_tp factory call, everything else
  // (priors, the likelihood lines, the double-mode instantiations and the
  // write_array output path) stays stock
  for (i in 1 : N) {
    y_hat[i] = beta[1] + beta[2] * x1[i] + beta[3] * x2[i]
               + beta[4] * x3[i] + a[idx1[i]] + b[idx2[i]];
  }
  // fires: a second predictor with the slope2 and slot-sharing leaf shapes
  // (beta[2] and beta[3] share the coefficient vector with the intercept)
  for (i in 1 : N) {
    y_hat2[i] = beta[1] + beta[2] * x1[i] * x2[i] + a[idx1[i]]
                + beta[3] * x3[i];
  }
  // does NOT fire: the predictor is read after its likelihood (sum(y) is
  // not the allowed whole-vector lpmf-argument use)
  for (i in 1 : N) {
    y_neg_read[i] = beta[1] + beta[2] * x1[i] + a[idx1[i]];
  }
  // does NOT fire: the predictor is printed
  for (i in 1 : N) {
    y_neg_print[i] = beta[1] + beta[2] * x1[i] + a[idx1[i]];
  }
  // does NOT fire: the predictor is read in generated quantities
  for (i in 1 : N) {
    y_neg_gq[i] = beta[1] + beta[2] * x1[i] + a[idx1[i]];
  }
  // does NOT fire: the predictor is partially indexed
  for (i in 1 : N) {
    y_neg_partial[i] = beta[1] + beta[2] * x1[i] + a[idx1[i]];
  }
  // does NOT fire: a nonlinear leaf (square of the data term)
  for (i in 1 : N) {
    y_neg_nonlin[i] = beta[1] + beta[2] * square(x1[i]) + a[idx1[i]];
  }
  // does NOT fire: the loop bound is not the plain data variable (N - 1)
  for (i in 1 : N - 1) {
    y_neg_bound[i] = beta[1] + beta[2] * x1[i] + a[idx1[i]];
  }
  // does NOT fire: the consuming density is not a bernoulli_logit lpmf
  for (i in 1 : N) {
    y_neg_otherhead[i] = beta[1] + beta[2] * x1[i] + a[idx1[i]];
  }
  // does NOT fire: no downstream likelihood consumes the predictor
  for (i in 1 : N) {
    y_neg_nolike[i] = beta[1] + beta[2] * x1[i] + a[idx1[i]];
  }
  // does NOT fire: a gathered coefficient times data (a[...] * x1[i]) is
  // outside the leaf vocabulary
  for (i in 1 : N) {
    y_neg_gather_slope[i] = beta[1] + a[idx1[i]] * x1[i] + b[idx2[i]];
  }
  // does NOT fire: a scalar predictor assigned in a loop (no elementwise
  // vector assignment to match)
  for (i in 1 : N) {
    y_neg_scalar = beta[1] + beta[2] * x1[i] + a[idx1[i]];
  }
}
model {
  a ~ normal(mu_a, 2);
  b ~ normal(0, 2);
  beta ~ normal(0, 5);
  mu_a ~ normal(0, 1);
  sigma ~ cauchy(0, 1);
  y ~ bernoulli_logit(y_hat);
  y ~ bernoulli_logit(y_hat2);
  y ~ bernoulli_logit(y_neg_read);
  y ~ bernoulli_logit(y_neg_print);
  y ~ bernoulli_logit(y_neg_gq);
  y ~ bernoulli_logit(y_neg_partial);
  y ~ bernoulli_logit(y_neg_nonlin);
  y ~ bernoulli_logit(y_neg_bound);
  y2 ~ normal(y_neg_otherhead, sigma);
  y ~ bernoulli_logit(y_neg_gather_slope);
  y ~ bernoulli_logit(y_neg_scalar);
  target += normal_lpdf(sum(y_neg_read) | 0, 1);
  target += normal_lpdf(y_neg_partial[1] | 0, 1);
  print(y_neg_print);
}
generated quantities {
  real m_gq = mean(y_neg_gq);
}
