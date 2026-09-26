// Models for the two historical cards. Deterministic, so the page and the calibration agree.
(function (root) {
  // mulberry32: small deterministic PRNG
  function rng(seed) { return function () { seed |= 0; seed = seed + 0x6D2B79F5 | 0; let t = Math.imul(seed ^ seed >>> 15, 1 | seed); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }

  // Vancouver Stock Exchange index, January 1982 to 25 November 1983 (about 478 trading days).
  // Each update multiplies the index by (1 + r). The 1982 system truncated to 3 decimals after
  // every update; the fix rounds to nearest. The market drift is solved so the full-precision
  // index ends at 1098.892, the value recomputed in November 1983.
  function vancouver(updatesPerDay, days, seed) {
    const n = updatesPerDay * days, r = new Float64Array(n), g = rng(seed);
    const sigma = 1.8e-4;                                  // about 1% daily volatility
    for (let i = 0; i < n; i++) { const u = g() + g() + g() - 1.5; r[i] = sigma * u * 2; }
    let mu = 0;                                            // two Newton steps on sum log(1 + mu + r) = log(1.098892)
    for (let it = 0; it < 2; it++) {
      let lg = 0, d = 0;
      for (let i = 0; i < n; i++) { lg += Math.log1p(mu + r[i]); d += 1 / (1 + mu + r[i]); }
      mu += (Math.log(1.098892) - lg) / d;
    }
    for (let i = 0; i < n; i++) r[i] += mu;
    return { n, r, updatesPerDay, days };
  }
  // State is kept in integer thousandths, the way the index was stored.
  function vancouverStep(state, model, count) {
    const end = Math.min(model.n, state.i + count);
    for (let i = state.i; i < end; i++) {
      const f = 1 + model.r[i];
      state.trunc = Math.floor(state.trunc * f);
      state.round = Math.round(state.round * f);
      state.exact *= f;
    }
    state.i = end;
  }
  function vancouverStart() { return { i: 0, trunc: 1000000, round: 1000000, exact: 1000 }; }

  // Patriot clock: tenths of a second counted as an integer, converted to seconds by
  // multiplying by 1/10 chopped to 23 fractional bits (24-bit register), as the GAO describes.
  const CHOPPED_TENTH = Math.floor(0.1 * 2 ** 23) / 2 ** 23;          // 0.099999904632568359375
  const patriot = {
    choppedTime: ticks => ticks * CHOPPED_TENTH,
    exactTime: ticks => ticks / 10,
    gateShiftPerSecond: 2000,                                          // reproduces every shift in the GAO table
    CHOPPED_TENTH,
  };
  root.LabModels = { rng, vancouver, vancouverStep, vancouverStart, patriot };
})(typeof globalThis !== 'undefined' ? globalThis : this);
