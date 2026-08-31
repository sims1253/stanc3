data {
  int<lower=0> N;
  vector[N] y1;
  vector[N] y2;
  vector[N] y3;
  vector[N] x1;
  vector[N] x2;
  matrix[N, 2] X;
}
transformed data {
  vector[N] z; // transformed data is still data-typed: may fire
  z = 2 * x1 + 1;
}
parameters {
  real alpha;
  real b1;
  real b2;
  vector[2] beta;
  vector[N] theta; // parameter vector: predictor must not fire on it
  real<lower=0> sigma;
  vector<lower=0>[N] sigma_vec; // vector scale: must not fire
}
model {
  // firing: K=1 data-vector predictor, scalar intercept + slope
  y1 ~ normal(alpha + b1 * x1, sigma);
  // firing: K=2 data-vector chain (design synthesis via append_col)
  y2 ~ normal(alpha + b1 * x1 + b2 * x2, sigma);
  // firing: matrix predictor without intercept (stock --O1 form)
  y1 ~ normal(X * beta, sigma);
  // firing: matrix predictor with intercept
  y2 ~ normal(alpha + X * beta, sigma);
  // firing: K=1 without intercept
  y2 ~ normal(b1 * x1, sigma);
  // firing: subtracted slope
  y2 ~ normal(alpha - b1 * x1, sigma);
  // firing: nested (right-associated) chain
  y2 ~ normal(b1 * x1 + (alpha + b2 * x2), sigma);
  // firing: transformed-data response (the logmesquite class)
  z ~ normal(alpha + b1 * x1, sigma);
  // non-firing: nonlinear predictor
  y3 ~ normal(alpha + b1 * square(x1), sigma);
  // non-firing: parameter-vector predictor
  y3 ~ normal(alpha + b1 * theta, sigma);
  // non-firing: vector scale
  y3 ~ normal(alpha + b1 * x1, sigma_vec);
  // non-firing: parameter response
  theta ~ normal(alpha + b1 * x1, sigma);
  // non-firing: scalar broadcast predictor
  y3 ~ normal(alpha + b1 * x1[1], sigma);
  // non-firing: non-normal head
  y3 ~ cauchy(alpha + b1 * x1, sigma);
  alpha ~ normal(0, 1);
  b1 ~ normal(0, 1);
  b2 ~ normal(0, 1);
  beta ~ normal(0, 1);
  theta ~ normal(0, 1);
  sigma ~ cauchy(0, 2.5);
  sigma_vec ~ cauchy(0, 2.5);
}
