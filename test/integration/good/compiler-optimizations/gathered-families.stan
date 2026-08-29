data {
  int<lower=1> N;
  int<lower=1> J;
  int<lower=1> E;
  array[N] int<lower=1, upper=J> county_idx;
  array[N] int<lower=1, upper=J> county2_idx;
  array[E] int<lower=1, upper=J> node1;
  array[E] int<lower=1, upper=J> node2;
  vector[N] y;
  vector[N] x;
}
parameters {
  vector[J] alpha;
  vector[J] beta;
  vector[J] phi;
  vector[J] psi;
  real<lower=0> sigma;
  vector<lower=0>[N] sigma_v;
}
model {
  vector[N] mu1;
  vector[N] mu2;
  vector[N] mu3;
  vector[N] mu4;
  vector[N] mu5;
  vector[N] mu6;
  // gathered, loop class, shape A: mu[n] = alpha[county_idx[n]] (fires at
  // --O1 and up, reverse-mode instantiation only; the loop, its mu
  // declaration and the per-element lpdf are replaced by the primitive call
  // plus the per-term accumulator pushes)
  for (n in 1 : N) {
    mu1[n] = alpha[county_idx[n]];
    target += normal_lpdf(y[n] | mu1[n], sigma);
  }
  // gathered, loop class, shape B: mu[n] = alpha[ii[n]] + x[n] * beta[ii[n]]
  // (the same index vector; the --O1 multiply-add fusion turns the eta into
  // fma(x[n], beta[ii[n]], alpha[ii[n]]), which the matcher also accepts)
  for (n in 1 : N) {
    mu2[n] = alpha[county2_idx[n]] + x[n] * beta[county2_idx[n]];
    target += normal_lpdf(y[n] | mu2[n], sigma);
  }
  // gathered, expression class (ICAR): dot_self over a difference of two
  // gathers of the SAME vector; the -0.5 and the target += stay untouched
  target += -0.5 * dot_self(phi[node1] - phi[node2]);
  // not gathered (ICAR): the two gathers are of DIFFERENT vectors
  target += -0.5 * dot_self(phi[node1] - psi[node2]);
  // not gathered (ICAR): a sum, not a difference
  target += -0.5 * dot_self(phi[node1] + phi[node2]);
  // not gathered (ICAR): a single gather
  target += -0.5 * dot_self(phi[node1]);
  // not gathered (loop): mu is read after the loop
  for (n in 1 : N) {
    mu3[n] = alpha[county_idx[n]];
    target += normal_lpdf(y[n] | mu3[n], sigma);
  }
  target += normal_lpdf(sum(mu3) | 0, 1);
  // not gathered (loop): a different scalar density head
  for (n in 1 : N) {
    mu4[n] = alpha[county_idx[n]];
    target += cauchy_lpdf(y[n] | mu4[n], sigma);
  }
  // not gathered (loop): the index expression is not purely n-dependent
  for (n in 1 : N) {
    mu5[n] = alpha[county2_idx[county_idx[n]]];
    target += normal_lpdf(y[n] | mu5[n], sigma);
  }
  // not gathered (loop): sigma is indexed by the loop variable
  for (n in 1 : N) {
    mu6[n] = alpha[county_idx[n]];
    target += normal_lpdf(y[n] | mu6[n], sigma_v[n]);
  }
}
