functions {
  // the partial-credit user function: softmax over the cumulative sums of
  // (0, theta - beta), categorical on the 1-shifted response
  real pcm(int y, real theta, vector beta) {
    vector[rows(beta) + 1] unsummed;
    vector[rows(beta) + 1] probs;
    unsummed = append_row(rep_vector(0.0, 1), theta - beta);
    probs = softmax(cumulative_sum(unsummed));
    return categorical_lpmf(y + 1 | probs);
  }
  // not matched: the softmax result is read inside the function (an extra
  // use of the intermediate vector — the inlined body carries an if)
  real pcm_extra_use(int y, real theta, vector beta) {
    vector[rows(beta) + 1] unsummed;
    vector[rows(beta) + 1] probs;
    unsummed = append_row(rep_vector(0.0, 1), theta - beta);
    probs = softmax(cumulative_sum(unsummed));
    if (probs[1] > 2) {
      return negative_infinity();
    }
    return categorical_lpmf(y + 1 | probs);
  }
  // not matched: cumulative_sum reused inside the function
  real pcm_cumsum_reused(int y, real theta, vector beta) {
    vector[rows(beta) + 1] unsummed;
    vector[rows(beta) + 1] probs;
    real extra;
    unsummed = append_row(rep_vector(0.0, 1), theta - beta);
    extra = cumulative_sum(unsummed)[1];
    probs = softmax(cumulative_sum(unsummed));
    return categorical_lpmf(y + 1 | probs) + extra;
  }
}
data {
  int<lower=1> I;
  int<lower=1> N;
  array[N] int<lower=1, upper=I> ii;
  array[N] int<lower=1, upper=I> jj;
  array[N] int<lower=0> y;
  array[I] int m;
  array[I] int pos;
}
parameters {
  vector[I] alpha;
  vector[I] theta;
  vector[N] theta_v;
  vector[sum(m)] beta;
}
model {
  alpha ~ normal(0, 1);
  theta ~ normal(0, 1);
  theta_v ~ normal(0, 1);
  beta ~ normal(0, 3);
  // gathered pcm, the composed user-function loop class: fires at --O1 and
  // up (reverse-mode instantiation only; the inlined
  // softmax(cumulative_sum(append_row(0, ...))) loop is replaced by the
  // pcm_lpdf_gathered call plus the per-term accumulator pushes)
  for (n in 1 : N) {
    target += pcm(y[n], theta[jj[n]] .* alpha[ii[n]],
                  segment(beta, pos[ii[n]], m[ii[n]]));
  }
  // gathered pcm, commuted spelling: also fires (the matcher swaps both
  // bilinear bindings when the segment matches the first operand's index)
  for (n in 1 : N) {
    target += pcm(y[n], alpha[ii[n]] .* theta[jj[n]],
                  segment(beta, pos[ii[n]], m[ii[n]]));
  }
  // not gathered: the softmax result read elsewhere (pcm_extra_use)
  for (n in 1 : N) {
    target += pcm_extra_use(y[n], theta[jj[n]] .* alpha[ii[n]],
                            segment(beta, pos[ii[n]], m[ii[n]]));
  }
  // not gathered: cumulative_sum reused (pcm_cumsum_reused)
  for (n in 1 : N) {
    target += pcm_cumsum_reused(y[n], theta[jj[n]] .* alpha[ii[n]],
                                segment(beta, pos[ii[n]], m[ii[n]]));
  }
  // not gathered: a non-gathered bilinear operand (theta read at n)
  for (n in 1 : N) {
    target += pcm(y[n], theta_v[n] .* alpha[ii[n]],
                  segment(beta, pos[ii[n]], m[ii[n]]));
  }
  // not gathered: an extra statement in the likelihood loop body
  for (n in 1 : N) {
    target += pcm(y[n], theta[jj[n]] .* alpha[ii[n]],
                  segment(beta, pos[ii[n]], m[ii[n]]));
    if (y[n] < 0) {
      print("neg");
    }
  }
  // not gathered: the loop bound is not the response containers' length
  for (n in 1 : N - 1) {
    target += pcm(y[n], theta[jj[n]] .* alpha[ii[n]],
                  segment(beta, pos[ii[n]], m[ii[n]]));
  }
  // not gathered: dense accumulation outside the loop
  {
    vector[N] lp;
    for (n in 1 : N) {
      lp[n] = pcm(y[n], theta[jj[n]] .* alpha[ii[n]],
                  segment(beta, pos[ii[n]], m[ii[n]]));
    }
    target += sum(lp);
  }
}
