data {
  int<lower=0> N;
  array[N] int y1;
  array[N] int y2;
  array[N] int y4;
  matrix[N, 1] x;
}
transformed data {
  array[N] int z; // not a data-block variable: must NOT fire
  for (n in 1:N) {
    z[n] = y1[n];
  }
}
parameters {
  real alpha;
  vector[1] b1;
  real<lower=0> lambda;
}
transformed parameters {
  vector[N] eta = alpha + square(to_vector(x * b1)); // not glm-rewritable
}
model {
  // firing: plain poisson_log head with data y
  target += poisson_log_lpmf(y1 | eta);
  // firing: glm head, and the same y2 twice must reuse one hoist
  target += poisson_log_glm_lpmf(y2 | x, alpha, b1);
  target += poisson_log_glm_lpmf(y2 | x, alpha, 2 * b1);
  // non-firing: wrong head (poisson_lpmf, rate form)
  target += poisson_lpmf(y1 | lambda);
  // non-firing: unnormalized form already drops the constant
  target += poisson_log_lupmf(y1 | eta);
  // non-firing: sampling statement is already propto
  y4 ~ poisson_log(alpha + x * b1);
  // non-firing: y is transformed data, not a data-block variable
  target += poisson_log_lpmf(z | eta);
  alpha ~ normal(0, 1);
  b1 ~ normal(0, 1);
  lambda ~ exponential(1);
}
