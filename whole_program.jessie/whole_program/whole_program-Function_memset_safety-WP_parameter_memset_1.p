fof(witness_sort, axiom, ![A]: (sort(A, witness(A)) = witness(A))).

fof(true_sort, axiom, (sort(bool, true1) = true1)).

fof(false_sort, axiom, (sort(bool, false1) = false1)).

fof(match_bool_sort, axiom, ![A]: ![X, X1, X2]: (sort(A, match_bool(A, X, X1,
  X2)) = match_bool(A, X, X1, X2))).

fof(match_bool_True, axiom, ![A]: ![Z, Z1]: (match_bool(A, true1, Z,
  Z1) = sort(A, Z))).

fof(match_bool_False, axiom, ![A]: ![Z, Z1]: (match_bool(A, false1, Z,
  Z1) = sort(A, Z1))).

fof(true_False, axiom, ~ (true1 = false1)).

fof(bool_inversion, axiom, ![U]: ((sort(bool, U) = true1) | (sort(bool,
  U) = false1))).

fof(tuple0_sort, axiom, (sort(tuple0, tuple01) = tuple01)).

fof(tuple0_inversion, axiom, ![U]: (sort(tuple0, U) = tuple01)).

fof(infix_lseq_def, axiom, ![X, Y]: (infix_lseq(X, Y) <=> (infix_ls(X, Y)
  | (X = Y)))).

fof(infix_pl_sort, axiom, ![X, X1]: (sort(int, infix_pl(X, X1)) = infix_pl(X,
  X1))).

fof(prefix_mn_sort, axiom, ![X]: (sort(int, prefix_mn(X)) = prefix_mn(X))).

fof(infix_as_sort, axiom, ![X, X1]: (sort(int, infix_as(X, X1)) = infix_as(X,
  X1))).

fof(assoc, axiom, ![X, Y, Z]: (infix_pl(infix_pl(X, Y), Z) = infix_pl(X,
  infix_pl(Y, Z)))).

fof(unit_def_l, axiom, ![X]: (infix_pl(const_0, X) = X)).

fof(unit_def_r, axiom, ![X]: (infix_pl(X, const_0) = X)).

fof(inv_def_l, axiom, ![X]: (infix_pl(prefix_mn(X), X) = const_0)).

fof(inv_def_r, axiom, ![X]: (infix_pl(X, prefix_mn(X)) = const_0)).

fof(comm, axiom, ![X, Y]: (infix_pl(X, Y) = infix_pl(Y, X))).

fof(assoc1, axiom, ![X, Y, Z]: (infix_as(infix_as(X, Y), Z) = infix_as(X,
  infix_as(Y, Z)))).

fof(mul_distr_l, axiom, ![X, Y, Z]: (infix_as(X, infix_pl(Y,
  Z)) = infix_pl(infix_as(X, Y), infix_as(X, Z)))).

fof(mul_distr_r, axiom, ![X, Y, Z]: (infix_as(infix_pl(Y, Z),
  X) = infix_pl(infix_as(Y, X), infix_as(Z, X)))).

fof(comm1, axiom, ![X, Y]: (infix_as(X, Y) = infix_as(Y, X))).

fof(unitary, axiom, ![X]: (infix_as(const_1, X) = X)).

fof(nonTrivialRing, axiom, ~ (const_0 = const_1)).

fof(infix_gteq_def, axiom, ![X, Y]: (infix_gteq(X, Y) <=> infix_lseq(Y, X))).

fof(refl, axiom, ![X]: infix_lseq(X, X)).

fof(trans, axiom, ![X, Y, Z]: (infix_lseq(X, Y) => (infix_lseq(Y, Z)
  => infix_lseq(X, Z)))).

fof(antisymm, axiom, ![X, Y]: (infix_lseq(X, Y) => (infix_lseq(Y, X)
  => (X = Y)))).

fof(total, axiom, ![X, Y]: (infix_lseq(X, Y) | infix_lseq(Y, X))).

fof(zeroLessOne, axiom, infix_lseq(const_0, const_1)).

fof(compatOrderAdd, axiom, ![X, Y, Z]: (infix_lseq(X, Y)
  => infix_lseq(infix_pl(X, Z), infix_pl(Y, Z)))).

fof(compatOrderMult, axiom, ![X, Y, Z]: (infix_lseq(X, Y)
  => (infix_lseq(const_0, Z) => infix_lseq(infix_as(X, Z), infix_as(Y,
  Z))))).

fof(abs_le, axiom, ![X, Y]: ((((infix_gteq(X, const_0) & infix_lseq(X, Y))
  | (~ infix_gteq(X, const_0) & infix_lseq(prefix_mn(X), Y)))
  => (infix_lseq(prefix_mn(Y), X) & infix_lseq(X, Y)))
  & ((infix_lseq(prefix_mn(Y), X) & infix_lseq(X, Y)) => ((infix_gteq(X,
  const_0) => infix_lseq(X, Y)) & (~ infix_gteq(X, const_0)
  => infix_lseq(prefix_mn(X), Y)))))).

fof(abs_pos, axiom, ![X]: (~ infix_gteq(X, const_0)
  => infix_gteq(prefix_mn(X), const_0))).

fof(div_sort, axiom, ![X, X1]: (sort(int, div(X, X1)) = div(X, X1))).

fof(mod_sort, axiom, ![X, X1]: (sort(int, mod(X, X1)) = mod(X, X1))).

fof(div_mod, axiom, ![X, Y]: (~ (Y = const_0) => (X = infix_pl(infix_as(Y,
  div(X, Y)), mod(X, Y))))).

fof(div_bound, axiom, ![X, Y]: ((infix_gteq(X, const_0) & infix_ls(const_0,
  Y)) => (infix_lseq(const_0, div(X, Y)) & infix_lseq(div(X, Y), X)))).

fof(mod_bound, axiom, ![X, Y]: (~ (Y = const_0) => (((infix_gteq(Y, const_0)
  => infix_ls(prefix_mn(Y), mod(X, Y))) & (~ infix_gteq(Y, const_0)
  => infix_ls(prefix_mn(prefix_mn(Y)), mod(X, Y)))) & ((infix_gteq(Y,
  const_0) => infix_ls(mod(X, Y), Y)) & (~ infix_gteq(Y, const_0)
  => infix_ls(mod(X, Y), prefix_mn(Y))))))).

fof(div_sign_pos, axiom, ![X, Y]: ((infix_gteq(X, const_0)
  & infix_ls(const_0, Y)) => infix_gteq(div(X, Y), const_0))).

fof(div_sign_neg, axiom, ![X, Y]: ((infix_lseq(X, const_0)
  & infix_ls(const_0, Y)) => infix_lseq(div(X, Y), const_0))).

fof(mod_sign_pos, axiom, ![X, Y]: ((infix_gteq(X, const_0) & ~ (Y = const_0))
  => infix_gteq(mod(X, Y), const_0))).

fof(mod_sign_neg, axiom, ![X, Y]: ((infix_lseq(X, const_0) & ~ (Y = const_0))
  => infix_lseq(mod(X, Y), const_0))).

fof(rounds_toward_zero, axiom, ![X, Y]: (~ (Y = const_0)
  => ((infix_gteq(infix_as(div(X, Y), Y), const_0) => ((infix_gteq(X,
  const_0) => infix_lseq(infix_as(div(X, Y), Y), X)) & (~ infix_gteq(X,
  const_0) => infix_lseq(infix_as(div(X, Y), Y), prefix_mn(X))))) & (~
  infix_gteq(infix_as(div(X, Y), Y), const_0) => ((infix_gteq(X, const_0)
  => infix_lseq(prefix_mn(infix_as(div(X, Y), Y)), X)) & (~ infix_gteq(X,
  const_0) => infix_lseq(prefix_mn(infix_as(div(X, Y), Y)),
  prefix_mn(X)))))))).

fof(div_1, axiom, ![X]: (div(X, const_1) = X)).

fof(mod_1, axiom, ![X]: (mod(X, const_1) = const_0)).

fof(div_inf, axiom, ![X, Y]: ((infix_lseq(const_0, X) & infix_ls(X, Y))
  => (div(X, Y) = const_0))).

fof(mod_inf, axiom, ![X, Y]: ((infix_lseq(const_0, X) & infix_ls(X, Y))
  => (mod(X, Y) = X))).

fof(div_mult, axiom, ![X, Y, Z]: ((infix_ls(const_0, X) & (infix_gteq(Y,
  const_0) & infix_gteq(Z, const_0))) => (div(infix_pl(infix_as(X, Y), Z),
  X) = infix_pl(Y, div(Z, X))))).

fof(mod_mult, axiom, ![X, Y, Z]: ((infix_ls(const_0, X) & (infix_gteq(Y,
  const_0) & infix_gteq(Z, const_0))) => (mod(infix_pl(infix_as(X, Y), Z),
  X) = mod(Z, X)))).

fof(div_mult_simplest, axiom, ![X, Y]: ((infix_gteq(X, const_0)
  & infix_ls(const_0, Y)) => (div(infix_as(X, Y), Y) = X))).

fof(to_int_sort, axiom, ![X]: (sort(int, to_int(X)) = to_int(X))).

fof(to_int_in_bounds, axiom, ![A]: (infix_lseq(const_0, to_int(A))
  & infix_lseq(to_int(A), const_18446744073709551615))).

fof(of_int_sort, axiom, ![X]: (sort(t, of_int(X)) = of_int(X))).

fof(of_int, axiom, ![A]: ((infix_lseq(const_0, A) & infix_lseq(A,
  const_18446744073709551615)) => (to_int(of_int(A)) = A))).

fof(extensionality1, axiom, ![X, Y]: ((to_int(X) = to_int(Y)) => (sort(t,
  X) = sort(t, Y)))).

fof(extensionality2, axiom, ![X, Y]: ((of_int(X) = of_int(Y))
  => (((infix_lseq(const_0, X) & infix_lseq(X, const_18446744073709551615))
  & (infix_lseq(const_0, Y) & infix_lseq(Y, const_18446744073709551615)))
  => (X = Y)))).

fof(infix_lseq_def1, axiom, ![A, B]: (infix_lseq1(A, B)
  <=> infix_lseq(to_int(A), to_int(B)))).

fof(infix_ls_def, axiom, ![A, B]: (infix_ls1(A, B) <=> infix_ls(to_int(A),
  to_int(B)))).

fof(infix_gteq_def1, axiom, ![A, B]: (infix_gteq1(A, B)
  <=> infix_gteq(to_int(A), to_int(B)))).

fof(infix_gt_def, axiom, ![A, B]: (infix_gt(A, B) <=> infix_ls(to_int(B),
  to_int(A)))).

fof(div_sort1, axiom, ![X, X1]: (sort(int, div1(X, X1)) = div1(X, X1))).

fof(mod_sort1, axiom, ![X, X1]: (sort(int, mod1(X, X1)) = mod1(X, X1))).

fof(div_mod1, axiom, ![X, Y]: (~ (Y = const_0) => (X = infix_pl(infix_as(Y,
  div1(X, Y)), mod1(X, Y))))).

fof(mod_bound1, axiom, ![X, Y]: (~ (Y = const_0) => (infix_lseq(const_0,
  mod1(X, Y)) & ((infix_gteq(Y, const_0) => infix_ls(mod1(X, Y), Y)) & (~
  infix_gteq(Y, const_0) => infix_ls(mod1(X, Y), prefix_mn(Y))))))).

fof(div_unique, axiom, ![X, Y, Q]: (infix_ls(const_0, Y)
  => ((infix_lseq(infix_as(Q, Y), X) & infix_ls(X, infix_pl(infix_as(Q, Y),
  Y))) => (div1(X, Y) = Q)))).

fof(div_bound1, axiom, ![X, Y]: ((infix_gteq(X, const_0) & infix_ls(const_0,
  Y)) => (infix_lseq(const_0, div1(X, Y)) & infix_lseq(div1(X, Y), X)))).

fof(mod_11, axiom, ![X]: (mod1(X, const_1) = const_0)).

fof(div_11, axiom, ![X]: (div1(X, const_1) = X)).

fof(div_inf1, axiom, ![X, Y]: ((infix_lseq(const_0, X) & infix_ls(X, Y))
  => (div1(X, Y) = const_0))).

fof(div_inf_neg, axiom, ![X, Y]: ((infix_ls(const_0, X) & infix_lseq(X, Y))
  => (div1(prefix_mn(X), Y) = prefix_mn(const_1)))).

fof(mod_0, axiom, ![Y]: (~ (Y = const_0) => (mod1(const_0, Y) = const_0))).

fof(div_1_left, axiom, ![Y]: (infix_ls(const_1, Y) => (div1(const_1,
  Y) = const_0))).

fof(div_minus1_left, axiom, ![Y]: (infix_ls(const_1, Y)
  => (div1(prefix_mn(const_1), Y) = prefix_mn(const_1)))).

fof(mod_1_left, axiom, ![Y]: (infix_ls(const_1, Y) => (mod1(const_1,
  Y) = const_1))).

fof(mod_minus1_left, axiom, ![Y]: (infix_ls(const_1, Y)
  => (mod1(prefix_mn(const_1), Y) = infix_pl(Y, prefix_mn(const_1))))).

fof(div_mult1, axiom, ![X, Y, Z]: (infix_ls(const_0, X)
  => (div1(infix_pl(infix_as(X, Y), Z), X) = infix_pl(Y, div1(Z, X))))).

fof(mod_mult1, axiom, ![X, Y, Z]: (infix_ls(const_0, X)
  => (mod1(infix_pl(infix_as(X, Y), Z), X) = mod1(Z, X)))).

fof(of_int_modulo_sort, axiom, ![X]: (sort(t,
  of_int_modulo(X)) = of_int_modulo(X))).

fof(of_int_const_sort, axiom, ![X]: (sort(t,
  of_int_const(X)) = of_int_const(X))).

fof(infix_plpc_sort, axiom, ![X, X1]: (sort(t, infix_plpc(X,
  X1)) = infix_plpc(X, X1))).

fof(infix_mnpc_sort, axiom, ![X, X1]: (sort(t, infix_mnpc(X,
  X1)) = infix_mnpc(X, X1))).

fof(prefix_mnpc_sort, axiom, ![X]: (sort(t,
  prefix_mnpc(X)) = prefix_mnpc(X))).

fof(infix_aspc_sort, axiom, ![X, X1]: (sort(t, infix_aspc(X,
  X1)) = infix_aspc(X, X1))).

fof(infix_slpc_sort, axiom, ![X, X1]: (sort(t, infix_slpc(X,
  X1)) = infix_slpc(X, X1))).

fof(infix_pcpc_sort, axiom, ![X, X1]: (sort(t, infix_pcpc(X,
  X1)) = infix_pcpc(X, X1))).

fof(extend_sort, axiom, ![X]: (sort(tt, extend(X)) = extend(X))).

fof(infix_plpctl_sort, axiom, ![X, X1]: (sort(tt, infix_plpctl(X,
  X1)) = infix_plpctl(X, X1))).

fof(infix_mnpctl_sort, axiom, ![X, X1]: (sort(tt, infix_mnpctl(X,
  X1)) = infix_mnpctl(X, X1))).

fof(prefix_mnpctl_sort, axiom, ![X]: (sort(tt,
  prefix_mnpctl(X)) = prefix_mnpctl(X))).

fof(infix_aspctl_sort, axiom, ![X, X1]: (sort(tt, infix_aspctl(X,
  X1)) = infix_aspctl(X, X1))).

fof(infix_slpctl_sort, axiom, ![X, X1]: (sort(tt, infix_slpctl(X,
  X1)) = infix_slpctl(X, X1))).

fof(infix_pcpctl_sort, axiom, ![X, X1]: (sort(tt, infix_pcpctl(X,
  X1)) = infix_pcpctl(X, X1))).

fof(infix_et_sort, axiom, ![X, X1]: (sort(t, infix_et(X, X1)) = infix_et(X,
  X1))).

fof(infix_brcf_sort, axiom, ![X, X1]: (sort(t, infix_brcf(X,
  X1)) = infix_brcf(X, X1))).

fof(prefix_tl_sort, axiom, ![X]: (sort(t, prefix_tl(X)) = prefix_tl(X))).

fof(infix_cf_sort, axiom, ![X, X1]: (sort(t, infix_cf(X, X1)) = infix_cf(X,
  X1))).

fof(lsl_sort, axiom, ![X, X1]: (sort(t, lsl(X, X1)) = lsl(X, X1))).

fof(lsl_modulo_sort, axiom, ![X, X1]: (sort(t, lsl_modulo(X,
  X1)) = lsl_modulo(X, X1))).

fof(lsr_sort, axiom, ![X, X1]: (sort(t, lsr(X, X1)) = lsr(X, X1))).

fof(asr_sort, axiom, ![X, X1]: (sort(t, asr(X, X1)) = asr(X, X1))).

fof(lsl_modulo__sort, axiom, ![X, X1]: (sort(tt, lsl_modulo_(X,
  X1)) = lsl_modulo_(X, X1))).

fof(of_int_modulo, axiom, ![N]: (to_int(of_int_modulo(N)) = infix_pl(const_0,
  mod1(infix_pl(N, prefix_mn(const_0)),
  infix_pl(infix_pl(const_18446744073709551615, prefix_mn(const_0)),
  const_1))))).

fof(add_modulo, axiom, ![A, B]: (to_int(infix_plpc(A, B)) = infix_pl(const_0,
  mod1(infix_pl(infix_pl(to_int(A), to_int(B)), prefix_mn(const_0)),
  infix_pl(infix_pl(const_18446744073709551615, prefix_mn(const_0)),
  const_1))))).

fof(neg_modulo, axiom, ![A]: (to_int(prefix_mnpc(A)) = infix_pl(const_0,
  mod1(infix_pl(prefix_mn(to_int(A)), prefix_mn(const_0)),
  infix_pl(infix_pl(const_18446744073709551615, prefix_mn(const_0)),
  const_1))))).

fof(sub_modulo, axiom, ![A, B]: (to_int(infix_mnpc(A, B)) = infix_pl(const_0,
  mod1(infix_pl(infix_pl(to_int(A), prefix_mn(to_int(B))),
  prefix_mn(const_0)), infix_pl(infix_pl(const_18446744073709551615,
  prefix_mn(const_0)), const_1))))).

fof(mult_modulo, axiom, ![A, B]: (to_int(infix_aspc(A,
  B)) = infix_pl(const_0, mod1(infix_pl(infix_as(to_int(A), to_int(B)),
  prefix_mn(const_0)), infix_pl(infix_pl(const_18446744073709551615,
  prefix_mn(const_0)), const_1))))).

fof(div_modulo, axiom, ![A, B]: (to_int(infix_slpc(A, B)) = infix_pl(const_0,
  mod1(infix_pl(div(to_int(A), to_int(B)), prefix_mn(const_0)),
  infix_pl(infix_pl(const_18446744073709551615, prefix_mn(const_0)),
  const_1))))).

fof(mod_modulo, axiom, ![A, B]: (to_int(infix_pcpc(A, B)) = mod(to_int(A),
  to_int(B)))).

fof(power2_sort, axiom, ![X]: (sort(int, power2(X)) = power2(X))).

fof(powers_of_2, axiom, ((power2(const_0) = const_1)
  & ((power2(const_1) = const_2) & ((power2(const_2) = const_4)
  & ((power2(const_3) = const_8) & ((power2(const_4) = const_16)
  & ((power2(const_5) = const_32) & ((power2(const_6) = const_64)
  & ((power2(const_7) = const_128) & ((power2(const_8) = const_256)
  & ((power2(const_9) = const_512) & ((power2(const_10) = const_1024)
  & ((power2(const_11) = const_2048) & ((power2(const_12) = const_4096)
  & ((power2(const_13) = const_8192) & ((power2(const_14) = const_16384)
  & ((power2(const_15) = const_32768) & ((power2(const_16) = const_65536)
  & ((power2(const_17) = const_131072) & ((power2(const_18) = const_262144)
  & ((power2(const_19) = const_524288) & ((power2(const_20) = const_1048576)
  & ((power2(const_21) = const_2097152) & ((power2(const_22) = const_4194304)
  & ((power2(const_23) = const_8388608)
  & ((power2(const_24) = const_16777216)
  & ((power2(const_25) = const_33554432)
  & ((power2(const_26) = const_67108864)
  & ((power2(const_27) = const_134217728)
  & ((power2(const_28) = const_268435456)
  & ((power2(const_29) = const_536870912)
  & ((power2(const_30) = const_1073741824)
  & ((power2(const_31) = const_2147483648)
  & ((power2(const_32) = const_4294967296)
  & ((power2(const_33) = const_8589934592)
  & ((power2(const_34) = const_17179869184)
  & ((power2(const_35) = const_34359738368)
  & ((power2(const_36) = const_68719476736)
  & ((power2(const_37) = const_137438953472)
  & ((power2(const_38) = const_274877906944)
  & ((power2(const_39) = const_549755813888)
  & ((power2(const_40) = const_1099511627776)
  & ((power2(const_41) = const_2199023255552)
  & ((power2(const_42) = const_4398046511104)
  & ((power2(const_43) = const_8796093022208)
  & ((power2(const_44) = const_17592186044416)
  & ((power2(const_45) = const_35184372088832)
  & ((power2(const_46) = const_70368744177664)
  & ((power2(const_47) = const_140737488355328)
  & ((power2(const_48) = const_281474976710656)
  & ((power2(const_49) = const_562949953421312)
  & ((power2(const_50) = const_1125899906842624)
  & ((power2(const_51) = const_2251799813685248)
  & ((power2(const_52) = const_4503599627370496)
  & ((power2(const_53) = const_9007199254740992)
  & ((power2(const_54) = const_18014398509481984)
  & ((power2(const_55) = const_36028797018963968)
  & ((power2(const_56) = const_72057594037927936)
  & ((power2(const_57) = const_144115188075855872)
  & ((power2(const_58) = const_288230376151711744)
  & ((power2(const_59) = const_576460752303423488)
  & ((power2(const_60) = const_1152921504606846976)
  & ((power2(const_61) = const_2305843009213693952)
  & ((power2(const_62) = const_4611686018427387904)
  & ((power2(const_63) = const_9223372036854775808)
  & (power2(const_64) = const_18446744073709551616)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

fof(val_two_power_size, axiom,
  (power2(const_64) = infix_pl(infix_pl(const_18446744073709551615,
  prefix_mn(const_0)), const_1))).

fof(of_int_const, axiom, ![N]: (of_int_const(N) = of_int(N))).

fof(of_int_def, axiom, ![N]: ((infix_lseq(const_0, N) & infix_lseq(N,
  const_18446744073709551615)) => (of_int(N) = of_int_modulo(N)))).

fof(lt_eq, axiom, ![A, B]: (infix_ls1(A, B) <=> lt(A, B))).

fof(le_eq, axiom, ![A, B]: (infix_lseq1(A, B) <=> le(A, B))).

fof(gt_eq, axiom, ![A, B]: (infix_gt(A, B) <=> gt(A, B))).

fof(ge_eq, axiom, ![A, B]: (infix_gteq1(A, B) <=> ge(A, B))).

fof(nth, axiom, ![A]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N, const_64))
  => (nth(A, N) <=> ((infix_gteq(to_int(A), const_0)
  & infix_gteq(mod(to_int(A), power2(infix_pl(N, const_1))), power2(N)))
  | (infix_ls(to_int(A), const_0)
  & infix_gteq(mod(infix_pl(infix_pl(infix_pl(const_18446744073709551615,
  prefix_mn(const_0)), const_1), to_int(A)), power2(infix_pl(N, const_1))),
  power2(N))))))).

fof(nth_bw_and, axiom, ![A, B]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_64)) => (nth(infix_et(A, B), N) <=> (nth(A, N) & nth(B, N))))).

fof(nth_bw_or, axiom, ![A, B]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_64)) => (nth(infix_brcf(A, B), N) <=> (nth(A, N) | nth(B, N))))).

fof(nth_bw_xor, axiom, ![A, B]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_64)) => (nth(infix_cf(A, B), N) <=> ~ (nth(A, N) <=> nth(B, N))))).

fof(nth_bw_not, axiom, ![A]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_64)) => (nth(prefix_tl(A), N) <=> ~ nth(A, N)))).

fof(lsr_nth_low, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int(S))
  & infix_ls(to_int(S), const_64)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_64)) => (infix_ls(infix_pl(N, to_int(S)), const_64) => (nth(lsr(B,
  S), N) <=> nth(B, infix_pl(N, to_int(S)))))))).

fof(lsr_nth_high, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int(S))
  & infix_ls(to_int(S), const_64)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_64)) => (infix_gteq(infix_pl(N, to_int(S)), const_64) => ~ nth(lsr(B,
  S), N))))).

fof(asr_nth_low, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int(S))
  & infix_ls(to_int(S), const_64)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_64)) => ((infix_lseq(const_0, infix_pl(N, to_int(S)))
  & infix_ls(infix_pl(N, to_int(S)), const_64)) => (nth(asr(B, S), N)
  <=> nth(B, infix_pl(N, to_int(S)))))))).

fof(asr_nth_high, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int(S))
  & infix_ls(to_int(S), const_64)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_64)) => (infix_gteq(infix_pl(N, to_int(S)), const_64) => (nth(asr(B,
  S), N) <=> nth(B, infix_pl(const_64, prefix_mn(const_1)))))))).

fof(lsl_modulo_nth_high, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0,
  to_int(S)) & infix_ls(to_int(S), const_64)) => ((infix_lseq(const_0, N)
  & infix_ls(N, const_64)) => ((infix_lseq(const_0, infix_pl(N,
  prefix_mn(to_int(S)))) & infix_ls(infix_pl(N, prefix_mn(to_int(S))),
  const_64)) => (nth(lsl_modulo(B, S), N) <=> nth(B, infix_pl(N,
  prefix_mn(to_int(S))))))))).

fof(lsl_modulo_nth_low, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0,
  to_int(S)) & infix_ls(to_int(S), const_64)) => ((infix_lseq(const_0, N)
  & infix_ls(N, const_64)) => (infix_ls(infix_pl(N, prefix_mn(to_int(S))),
  const_0) => ~ nth(lsl_modulo(B, S), N))))).

fof(lsl, axiom, ![B]: ![S]: ((infix_lseq(const_0, to_int(S))
  & infix_ls(to_int(S), const_64)) => ((lsr(lsl_modulo(B, S), S) = S)
  => (lsl(B, S) = lsl_modulo(B, S))))).

fof(lsr_unsigned, axiom, ![A]: ![N]: ((infix_lseq(const_0, to_int(N))
  & infix_ls(to_int(N), const_64)) => (to_int(lsr(A, N)) = div1(to_int(A),
  power2(to_int(N)))))).

fof(asr_signed, axiom, $true).

fof(lsl_modulo, axiom, ![A]: ![N]: ((infix_lseq(const_0, to_int(N))
  & infix_ls(to_int(N), const_64)) => (to_int(lsl_modulo(A,
  N)) = infix_pl(const_0, mod1(infix_pl(infix_as(to_int(A),
  power2(to_int(N))), prefix_mn(const_0)),
  infix_pl(infix_pl(const_18446744073709551615, prefix_mn(const_0)),
  const_1)))))).

fof(to_int_sort1, axiom, ![X]: (sort(int, to_int1(X)) = to_int1(X))).

fof(to_int_in_bounds1, axiom, ![A]: (infix_lseq(prefix_mn(const_128),
  to_int1(A)) & infix_lseq(to_int1(A), const_127))).

fof(of_int_sort1, axiom, ![X]: (sort(t1, of_int1(X)) = of_int1(X))).

fof(of_int1, axiom, ![A]: ((infix_lseq(prefix_mn(const_128), A)
  & infix_lseq(A, const_127)) => (to_int1(of_int1(A)) = A))).

fof(extensionality11, axiom, ![X, Y]: ((to_int1(X) = to_int1(Y)) => (sort(t1,
  X) = sort(t1, Y)))).

fof(extensionality21, axiom, ![X, Y]: ((of_int1(X) = of_int1(Y))
  => (((infix_lseq(prefix_mn(const_128), X) & infix_lseq(X, const_127))
  & (infix_lseq(prefix_mn(const_128), Y) & infix_lseq(Y, const_127)))
  => (X = Y)))).

fof(infix_lseq_def2, axiom, ![A, B]: (infix_lseq2(A, B)
  <=> infix_lseq(to_int1(A), to_int1(B)))).

fof(infix_ls_def1, axiom, ![A, B]: (infix_ls2(A, B) <=> infix_ls(to_int1(A),
  to_int1(B)))).

fof(infix_gteq_def2, axiom, ![A, B]: (infix_gteq2(A, B)
  <=> infix_gteq(to_int1(A), to_int1(B)))).

fof(infix_gt_def1, axiom, ![A, B]: (infix_gt1(A, B) <=> infix_ls(to_int1(B),
  to_int1(A)))).

fof(to_int_sort2, axiom, ![X]: (sort(int, to_int2(X)) = to_int2(X))).

fof(to_int_in_bounds2, axiom, ![A]: (infix_lseq(prefix_mn(const_2147483648),
  to_int2(A)) & infix_lseq(to_int2(A), const_2147483647))).

fof(of_int_sort2, axiom, ![X]: (sort(t2, of_int2(X)) = of_int2(X))).

fof(of_int2, axiom, ![A]: ((infix_lseq(prefix_mn(const_2147483648), A)
  & infix_lseq(A, const_2147483647)) => (to_int2(of_int2(A)) = A))).

fof(extensionality12, axiom, ![X, Y]: ((to_int2(X) = to_int2(Y)) => (sort(t2,
  X) = sort(t2, Y)))).

fof(extensionality22, axiom, ![X, Y]: ((of_int2(X) = of_int2(Y))
  => (((infix_lseq(prefix_mn(const_2147483648), X) & infix_lseq(X,
  const_2147483647)) & (infix_lseq(prefix_mn(const_2147483648), Y)
  & infix_lseq(Y, const_2147483647))) => (X = Y)))).

fof(infix_lseq_def3, axiom, ![A, B]: (infix_lseq3(A, B)
  <=> infix_lseq(to_int2(A), to_int2(B)))).

fof(infix_ls_def2, axiom, ![A, B]: (infix_ls3(A, B) <=> infix_ls(to_int2(A),
  to_int2(B)))).

fof(infix_gteq_def3, axiom, ![A, B]: (infix_gteq3(A, B)
  <=> infix_gteq(to_int2(A), to_int2(B)))).

fof(infix_gt_def2, axiom, ![A, B]: (infix_gt2(A, B) <=> infix_ls(to_int2(B),
  to_int2(A)))).

fof(of_int_modulo_sort1, axiom, ![X]: (sort(t2,
  of_int_modulo1(X)) = of_int_modulo1(X))).

fof(of_int_const_sort1, axiom, ![X]: (sort(t2,
  of_int_const1(X)) = of_int_const1(X))).

fof(infix_plpc_sort1, axiom, ![X, X1]: (sort(t2, infix_plpc1(X,
  X1)) = infix_plpc1(X, X1))).

fof(infix_mnpc_sort1, axiom, ![X, X1]: (sort(t2, infix_mnpc1(X,
  X1)) = infix_mnpc1(X, X1))).

fof(prefix_mnpc_sort1, axiom, ![X]: (sort(t2,
  prefix_mnpc1(X)) = prefix_mnpc1(X))).

fof(infix_aspc_sort1, axiom, ![X, X1]: (sort(t2, infix_aspc1(X,
  X1)) = infix_aspc1(X, X1))).

fof(infix_slpc_sort1, axiom, ![X, X1]: (sort(t2, infix_slpc1(X,
  X1)) = infix_slpc1(X, X1))).

fof(infix_pcpc_sort1, axiom, ![X, X1]: (sort(t2, infix_pcpc1(X,
  X1)) = infix_pcpc1(X, X1))).

fof(extend_sort1, axiom, ![X]: (sort(tt1, extend1(X)) = extend1(X))).

fof(infix_plpctl_sort1, axiom, ![X, X1]: (sort(tt1, infix_plpctl1(X,
  X1)) = infix_plpctl1(X, X1))).

fof(infix_mnpctl_sort1, axiom, ![X, X1]: (sort(tt1, infix_mnpctl1(X,
  X1)) = infix_mnpctl1(X, X1))).

fof(prefix_mnpctl_sort1, axiom, ![X]: (sort(tt1,
  prefix_mnpctl1(X)) = prefix_mnpctl1(X))).

fof(infix_aspctl_sort1, axiom, ![X, X1]: (sort(tt1, infix_aspctl1(X,
  X1)) = infix_aspctl1(X, X1))).

fof(infix_slpctl_sort1, axiom, ![X, X1]: (sort(tt1, infix_slpctl1(X,
  X1)) = infix_slpctl1(X, X1))).

fof(infix_pcpctl_sort1, axiom, ![X, X1]: (sort(tt1, infix_pcpctl1(X,
  X1)) = infix_pcpctl1(X, X1))).

fof(infix_et_sort1, axiom, ![X, X1]: (sort(t2, infix_et1(X,
  X1)) = infix_et1(X, X1))).

fof(infix_brcf_sort1, axiom, ![X, X1]: (sort(t2, infix_brcf1(X,
  X1)) = infix_brcf1(X, X1))).

fof(prefix_tl_sort1, axiom, ![X]: (sort(t2, prefix_tl1(X)) = prefix_tl1(X))).

fof(infix_cf_sort1, axiom, ![X, X1]: (sort(t2, infix_cf1(X,
  X1)) = infix_cf1(X, X1))).

fof(lsl_sort1, axiom, ![X, X1]: (sort(t2, lsl1(X, X1)) = lsl1(X, X1))).

fof(lsl_modulo_sort1, axiom, ![X, X1]: (sort(t2, lsl_modulo1(X,
  X1)) = lsl_modulo1(X, X1))).

fof(lsr_sort1, axiom, ![X, X1]: (sort(t2, lsr1(X, X1)) = lsr1(X, X1))).

fof(asr_sort1, axiom, ![X, X1]: (sort(t2, asr1(X, X1)) = asr1(X, X1))).

fof(lsl_modulo__sort1, axiom, ![X, X1]: (sort(tt1, lsl_modulo_1(X,
  X1)) = lsl_modulo_1(X, X1))).

fof(of_int_modulo1, axiom, ![N]:
  (to_int2(of_int_modulo1(N)) = infix_pl(prefix_mn(const_2147483648),
  mod1(infix_pl(N, prefix_mn(prefix_mn(const_2147483648))),
  infix_pl(infix_pl(const_2147483647,
  prefix_mn(prefix_mn(const_2147483648))), const_1))))).

fof(add_modulo1, axiom, ![A, B]: (to_int2(infix_plpc1(A,
  B)) = infix_pl(prefix_mn(const_2147483648),
  mod1(infix_pl(infix_pl(to_int2(A), to_int2(B)),
  prefix_mn(prefix_mn(const_2147483648))),
  infix_pl(infix_pl(const_2147483647,
  prefix_mn(prefix_mn(const_2147483648))), const_1))))).

fof(neg_modulo1, axiom, ![A]:
  (to_int2(prefix_mnpc1(A)) = infix_pl(prefix_mn(const_2147483648),
  mod1(infix_pl(prefix_mn(to_int2(A)),
  prefix_mn(prefix_mn(const_2147483648))),
  infix_pl(infix_pl(const_2147483647,
  prefix_mn(prefix_mn(const_2147483648))), const_1))))).

fof(sub_modulo1, axiom, ![A, B]: (to_int2(infix_mnpc1(A,
  B)) = infix_pl(prefix_mn(const_2147483648),
  mod1(infix_pl(infix_pl(to_int2(A), prefix_mn(to_int2(B))),
  prefix_mn(prefix_mn(const_2147483648))),
  infix_pl(infix_pl(const_2147483647,
  prefix_mn(prefix_mn(const_2147483648))), const_1))))).

fof(mult_modulo1, axiom, ![A, B]: (to_int2(infix_aspc1(A,
  B)) = infix_pl(prefix_mn(const_2147483648),
  mod1(infix_pl(infix_as(to_int2(A), to_int2(B)),
  prefix_mn(prefix_mn(const_2147483648))),
  infix_pl(infix_pl(const_2147483647,
  prefix_mn(prefix_mn(const_2147483648))), const_1))))).

fof(div_modulo1, axiom, ![A, B]: (to_int2(infix_slpc1(A,
  B)) = infix_pl(prefix_mn(const_2147483648), mod1(infix_pl(div(to_int2(A),
  to_int2(B)), prefix_mn(prefix_mn(const_2147483648))),
  infix_pl(infix_pl(const_2147483647,
  prefix_mn(prefix_mn(const_2147483648))), const_1))))).

fof(mod_modulo1, axiom, ![A, B]: (to_int2(infix_pcpc1(A,
  B)) = mod(to_int2(A), to_int2(B)))).

fof(val_two_power_size1, axiom,
  (power2(const_32) = infix_pl(infix_pl(const_2147483647,
  prefix_mn(prefix_mn(const_2147483648))), const_1))).

fof(of_int_const1, axiom, ![N]: (of_int_const1(N) = of_int2(N))).

fof(of_int_def1, axiom, ![N]: ((infix_lseq(prefix_mn(const_2147483648), N)
  & infix_lseq(N, const_2147483647)) => (of_int2(N) = of_int_modulo1(N)))).

fof(lt_eq1, axiom, ![A, B]: (infix_ls3(A, B) <=> lt1(A, B))).

fof(le_eq1, axiom, ![A, B]: (infix_lseq3(A, B) <=> le1(A, B))).

fof(gt_eq1, axiom, ![A, B]: (infix_gt2(A, B) <=> gt1(A, B))).

fof(ge_eq1, axiom, ![A, B]: (infix_gteq3(A, B) <=> ge1(A, B))).

fof(nth1, axiom, ![A]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_32)) => (nth1(A, N) <=> ((infix_gteq(to_int2(A), const_0)
  & infix_gteq(mod(to_int2(A), power2(infix_pl(N, const_1))), power2(N)))
  | (infix_ls(to_int2(A), const_0)
  & infix_gteq(mod(infix_pl(infix_pl(infix_pl(const_2147483647,
  prefix_mn(prefix_mn(const_2147483648))), const_1), to_int2(A)),
  power2(infix_pl(N, const_1))), power2(N))))))).

fof(nth_bw_and1, axiom, ![A, B]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_32)) => (nth1(infix_et1(A, B), N) <=> (nth1(A, N) & nth1(B, N))))).

fof(nth_bw_or1, axiom, ![A, B]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_32)) => (nth1(infix_brcf1(A, B), N) <=> (nth1(A, N) | nth1(B, N))))).

fof(nth_bw_xor1, axiom, ![A, B]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_32)) => (nth1(infix_cf1(A, B), N) <=> ~ (nth1(A, N) <=> nth1(B,
  N))))).

fof(nth_bw_not1, axiom, ![A]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_32)) => (nth1(prefix_tl1(A), N) <=> ~ nth1(A, N)))).

fof(lsr_nth_low1, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int2(S))
  & infix_ls(to_int2(S), const_32)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_32)) => (infix_ls(infix_pl(N, to_int2(S)), const_32) => (nth1(lsr1(B,
  S), N) <=> nth1(B, infix_pl(N, to_int2(S)))))))).

fof(lsr_nth_high1, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int2(S))
  & infix_ls(to_int2(S), const_32)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_32)) => (infix_gteq(infix_pl(N, to_int2(S)), const_32) => ~
  nth1(lsr1(B, S), N))))).

fof(asr_nth_low1, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int2(S))
  & infix_ls(to_int2(S), const_32)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_32)) => ((infix_lseq(const_0, infix_pl(N, to_int2(S)))
  & infix_ls(infix_pl(N, to_int2(S)), const_32)) => (nth1(asr1(B, S), N)
  <=> nth1(B, infix_pl(N, to_int2(S)))))))).

fof(asr_nth_high1, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int2(S))
  & infix_ls(to_int2(S), const_32)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_32)) => (infix_gteq(infix_pl(N, to_int2(S)), const_32)
  => (nth1(asr1(B, S), N) <=> nth1(B, infix_pl(const_32,
  prefix_mn(const_1)))))))).

fof(lsl_modulo_nth_high1, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0,
  to_int2(S)) & infix_ls(to_int2(S), const_32)) => ((infix_lseq(const_0, N)
  & infix_ls(N, const_32)) => ((infix_lseq(const_0, infix_pl(N,
  prefix_mn(to_int2(S)))) & infix_ls(infix_pl(N, prefix_mn(to_int2(S))),
  const_32)) => (nth1(lsl_modulo1(B, S), N) <=> nth1(B, infix_pl(N,
  prefix_mn(to_int2(S))))))))).

fof(lsl_modulo_nth_low1, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0,
  to_int2(S)) & infix_ls(to_int2(S), const_32)) => ((infix_lseq(const_0, N)
  & infix_ls(N, const_32)) => (infix_ls(infix_pl(N, prefix_mn(to_int2(S))),
  const_0) => ~ nth1(lsl_modulo1(B, S), N))))).

fof(lsl1, axiom, ![B]: ![S]: ((infix_lseq(const_0, to_int2(S))
  & infix_ls(to_int2(S), const_32)) => ((lsr1(lsl_modulo1(B, S), S) = S)
  => (lsl1(B, S) = lsl_modulo1(B, S))))).

fof(lsr_unsigned1, axiom, $true).

fof(asr_signed1, axiom, ![A]: ![N]: ((infix_lseq(const_0, to_int2(N))
  & infix_ls(to_int2(N), const_32)) => (to_int2(asr1(A,
  N)) = div1(to_int2(A), power2(to_int2(N)))))).

fof(lsl_modulo1, axiom, ![A]: ![N]: ((infix_lseq(const_0, to_int2(N))
  & infix_ls(to_int2(N), const_32)) => (to_int2(lsl_modulo1(A,
  N)) = infix_pl(prefix_mn(const_2147483648),
  mod1(infix_pl(infix_as(to_int2(A), power2(to_int2(N))),
  prefix_mn(prefix_mn(const_2147483648))),
  infix_pl(infix_pl(const_2147483647,
  prefix_mn(prefix_mn(const_2147483648))), const_1)))))).

fof(to_int_def, axiom, ![A]: (to_int2(A) = infix_pl($ite_t(nth1(A, const_0),
  const_1, const_0), infix_pl($ite_t(nth1(A, const_1), const_2, const_0),
  infix_pl($ite_t(nth1(A, const_2), const_4, const_0),
  infix_pl($ite_t(nth1(A, const_3), const_8, const_0),
  infix_pl($ite_t(nth1(A, const_4), const_16, const_0),
  infix_pl($ite_t(nth1(A, const_5), const_32, const_0),
  infix_pl($ite_t(nth1(A, const_6), const_64, const_0),
  infix_pl($ite_t(nth1(A, const_7), const_128, const_0),
  infix_pl($ite_t(nth1(A, const_8), const_256, const_0),
  infix_pl($ite_t(nth1(A, const_9), const_512, const_0),
  infix_pl($ite_t(nth1(A, const_10), const_1024, const_0),
  infix_pl($ite_t(nth1(A, const_11), const_2048, const_0),
  infix_pl($ite_t(nth1(A, const_12), const_4096, const_0),
  infix_pl($ite_t(nth1(A, const_13), const_8192, const_0),
  infix_pl($ite_t(nth1(A, const_14), const_16384, const_0),
  infix_pl($ite_t(nth1(A, const_15), const_32768, const_0),
  infix_pl($ite_t(nth1(A, const_16), const_65536, const_0),
  infix_pl($ite_t(nth1(A, const_17), const_131072, const_0),
  infix_pl($ite_t(nth1(A, const_18), const_262144, const_0),
  infix_pl($ite_t(nth1(A, const_19), const_524288, const_0),
  infix_pl($ite_t(nth1(A, const_20), const_1048576, const_0),
  infix_pl($ite_t(nth1(A, const_21), const_2097152, const_0),
  infix_pl($ite_t(nth1(A, const_22), const_4194304, const_0),
  infix_pl($ite_t(nth1(A, const_23), const_8388608, const_0),
  infix_pl($ite_t(nth1(A, const_24), const_16777216, const_0),
  infix_pl($ite_t(nth1(A, const_25), const_33554432, const_0),
  infix_pl($ite_t(nth1(A, const_26), const_67108864, const_0),
  infix_pl($ite_t(nth1(A, const_27), const_134217728, const_0),
  infix_pl($ite_t(nth1(A, const_28), const_268435456, const_0),
  infix_pl($ite_t(nth1(A, const_29), const_536870912, const_0),
  infix_pl($ite_t(nth1(A, const_30), const_1073741824, const_0),
  $ite_t(nth1(A, const_31), prefix_mn(const_2147483648),
  const_0)))))))))))))))))))))))))))))))))).

fof(of_int_modulo_sort2, axiom, ![X]: (sort(t1,
  of_int_modulo2(X)) = of_int_modulo2(X))).

fof(of_int_const_sort2, axiom, ![X]: (sort(t1,
  of_int_const2(X)) = of_int_const2(X))).

fof(infix_plpc_sort2, axiom, ![X, X1]: (sort(t1, infix_plpc2(X,
  X1)) = infix_plpc2(X, X1))).

fof(infix_mnpc_sort2, axiom, ![X, X1]: (sort(t1, infix_mnpc2(X,
  X1)) = infix_mnpc2(X, X1))).

fof(prefix_mnpc_sort2, axiom, ![X]: (sort(t1,
  prefix_mnpc2(X)) = prefix_mnpc2(X))).

fof(infix_aspc_sort2, axiom, ![X, X1]: (sort(t1, infix_aspc2(X,
  X1)) = infix_aspc2(X, X1))).

fof(infix_slpc_sort2, axiom, ![X, X1]: (sort(t1, infix_slpc2(X,
  X1)) = infix_slpc2(X, X1))).

fof(infix_pcpc_sort2, axiom, ![X, X1]: (sort(t1, infix_pcpc2(X,
  X1)) = infix_pcpc2(X, X1))).

fof(extend_sort2, axiom, ![X]: (sort(tt2, extend2(X)) = extend2(X))).

fof(infix_plpctl_sort2, axiom, ![X, X1]: (sort(tt2, infix_plpctl2(X,
  X1)) = infix_plpctl2(X, X1))).

fof(infix_mnpctl_sort2, axiom, ![X, X1]: (sort(tt2, infix_mnpctl2(X,
  X1)) = infix_mnpctl2(X, X1))).

fof(prefix_mnpctl_sort2, axiom, ![X]: (sort(tt2,
  prefix_mnpctl2(X)) = prefix_mnpctl2(X))).

fof(infix_aspctl_sort2, axiom, ![X, X1]: (sort(tt2, infix_aspctl2(X,
  X1)) = infix_aspctl2(X, X1))).

fof(infix_slpctl_sort2, axiom, ![X, X1]: (sort(tt2, infix_slpctl2(X,
  X1)) = infix_slpctl2(X, X1))).

fof(infix_pcpctl_sort2, axiom, ![X, X1]: (sort(tt2, infix_pcpctl2(X,
  X1)) = infix_pcpctl2(X, X1))).

fof(infix_et_sort2, axiom, ![X, X1]: (sort(t1, infix_et2(X,
  X1)) = infix_et2(X, X1))).

fof(infix_brcf_sort2, axiom, ![X, X1]: (sort(t1, infix_brcf2(X,
  X1)) = infix_brcf2(X, X1))).

fof(prefix_tl_sort2, axiom, ![X]: (sort(t1, prefix_tl2(X)) = prefix_tl2(X))).

fof(infix_cf_sort2, axiom, ![X, X1]: (sort(t1, infix_cf2(X,
  X1)) = infix_cf2(X, X1))).

fof(lsl_sort2, axiom, ![X, X1]: (sort(t1, lsl2(X, X1)) = lsl2(X, X1))).

fof(lsl_modulo_sort2, axiom, ![X, X1]: (sort(t1, lsl_modulo2(X,
  X1)) = lsl_modulo2(X, X1))).

fof(lsr_sort2, axiom, ![X, X1]: (sort(t1, lsr2(X, X1)) = lsr2(X, X1))).

fof(asr_sort2, axiom, ![X, X1]: (sort(t1, asr2(X, X1)) = asr2(X, X1))).

fof(lsl_modulo__sort2, axiom, ![X, X1]: (sort(tt2, lsl_modulo_2(X,
  X1)) = lsl_modulo_2(X, X1))).

fof(of_int_modulo2, axiom, ![N]:
  (to_int1(of_int_modulo2(N)) = infix_pl(prefix_mn(const_128),
  mod1(infix_pl(N, prefix_mn(prefix_mn(const_128))),
  infix_pl(infix_pl(const_127, prefix_mn(prefix_mn(const_128))),
  const_1))))).

fof(add_modulo2, axiom, ![A, B]: (to_int1(infix_plpc2(A,
  B)) = infix_pl(prefix_mn(const_128), mod1(infix_pl(infix_pl(to_int1(A),
  to_int1(B)), prefix_mn(prefix_mn(const_128))), infix_pl(infix_pl(const_127,
  prefix_mn(prefix_mn(const_128))), const_1))))).

fof(neg_modulo2, axiom, ![A]:
  (to_int1(prefix_mnpc2(A)) = infix_pl(prefix_mn(const_128),
  mod1(infix_pl(prefix_mn(to_int1(A)), prefix_mn(prefix_mn(const_128))),
  infix_pl(infix_pl(const_127, prefix_mn(prefix_mn(const_128))),
  const_1))))).

fof(sub_modulo2, axiom, ![A, B]: (to_int1(infix_mnpc2(A,
  B)) = infix_pl(prefix_mn(const_128), mod1(infix_pl(infix_pl(to_int1(A),
  prefix_mn(to_int1(B))), prefix_mn(prefix_mn(const_128))),
  infix_pl(infix_pl(const_127, prefix_mn(prefix_mn(const_128))),
  const_1))))).

fof(mult_modulo2, axiom, ![A, B]: (to_int1(infix_aspc2(A,
  B)) = infix_pl(prefix_mn(const_128), mod1(infix_pl(infix_as(to_int1(A),
  to_int1(B)), prefix_mn(prefix_mn(const_128))), infix_pl(infix_pl(const_127,
  prefix_mn(prefix_mn(const_128))), const_1))))).

fof(div_modulo2, axiom, ![A, B]: (to_int1(infix_slpc2(A,
  B)) = infix_pl(prefix_mn(const_128), mod1(infix_pl(div(to_int1(A),
  to_int1(B)), prefix_mn(prefix_mn(const_128))), infix_pl(infix_pl(const_127,
  prefix_mn(prefix_mn(const_128))), const_1))))).

fof(mod_modulo2, axiom, ![A, B]: (to_int1(infix_pcpc2(A,
  B)) = mod(to_int1(A), to_int1(B)))).

fof(val_two_power_size2, axiom,
  (power2(const_8) = infix_pl(infix_pl(const_127,
  prefix_mn(prefix_mn(const_128))), const_1))).

fof(of_int_const2, axiom, ![N]: (of_int_const2(N) = of_int1(N))).

fof(of_int_def2, axiom, ![N]: ((infix_lseq(prefix_mn(const_128), N)
  & infix_lseq(N, const_127)) => (of_int1(N) = of_int_modulo2(N)))).

fof(lt_eq2, axiom, ![A, B]: (infix_ls2(A, B) <=> lt2(A, B))).

fof(le_eq2, axiom, ![A, B]: (infix_lseq2(A, B) <=> le2(A, B))).

fof(gt_eq2, axiom, ![A, B]: (infix_gt1(A, B) <=> gt2(A, B))).

fof(ge_eq2, axiom, ![A, B]: (infix_gteq2(A, B) <=> ge2(A, B))).

fof(nth2, axiom, ![A]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N, const_8))
  => (nth2(A, N) <=> ((infix_gteq(to_int1(A), const_0)
  & infix_gteq(mod(to_int1(A), power2(infix_pl(N, const_1))), power2(N)))
  | (infix_ls(to_int1(A), const_0)
  & infix_gteq(mod(infix_pl(infix_pl(infix_pl(const_127,
  prefix_mn(prefix_mn(const_128))), const_1), to_int1(A)), power2(infix_pl(N,
  const_1))), power2(N))))))).

fof(nth_bw_and2, axiom, ![A, B]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_8)) => (nth2(infix_et2(A, B), N) <=> (nth2(A, N) & nth2(B, N))))).

fof(nth_bw_or2, axiom, ![A, B]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_8)) => (nth2(infix_brcf2(A, B), N) <=> (nth2(A, N) | nth2(B, N))))).

fof(nth_bw_xor2, axiom, ![A, B]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_8)) => (nth2(infix_cf2(A, B), N) <=> ~ (nth2(A, N) <=> nth2(B,
  N))))).

fof(nth_bw_not2, axiom, ![A]: ![N]: ((infix_lseq(const_0, N) & infix_ls(N,
  const_8)) => (nth2(prefix_tl2(A), N) <=> ~ nth2(A, N)))).

fof(lsr_nth_low2, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int1(S))
  & infix_ls(to_int1(S), const_8)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_8)) => (infix_ls(infix_pl(N, to_int1(S)), const_8) => (nth2(lsr2(B,
  S), N) <=> nth2(B, infix_pl(N, to_int1(S)))))))).

fof(lsr_nth_high2, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int1(S))
  & infix_ls(to_int1(S), const_8)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_8)) => (infix_gteq(infix_pl(N, to_int1(S)), const_8) => ~
  nth2(lsr2(B, S), N))))).

fof(asr_nth_low2, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int1(S))
  & infix_ls(to_int1(S), const_8)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_8)) => ((infix_lseq(const_0, infix_pl(N, to_int1(S)))
  & infix_ls(infix_pl(N, to_int1(S)), const_8)) => (nth2(asr2(B, S), N)
  <=> nth2(B, infix_pl(N, to_int1(S)))))))).

fof(asr_nth_high2, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0, to_int1(S))
  & infix_ls(to_int1(S), const_8)) => ((infix_lseq(const_0, N) & infix_ls(N,
  const_8)) => (infix_gteq(infix_pl(N, to_int1(S)), const_8) => (nth2(asr2(B,
  S), N) <=> nth2(B, infix_pl(const_8, prefix_mn(const_1)))))))).

fof(lsl_modulo_nth_high2, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0,
  to_int1(S)) & infix_ls(to_int1(S), const_8)) => ((infix_lseq(const_0, N)
  & infix_ls(N, const_8)) => ((infix_lseq(const_0, infix_pl(N,
  prefix_mn(to_int1(S)))) & infix_ls(infix_pl(N, prefix_mn(to_int1(S))),
  const_8)) => (nth2(lsl_modulo2(B, S), N) <=> nth2(B, infix_pl(N,
  prefix_mn(to_int1(S))))))))).

fof(lsl_modulo_nth_low2, axiom, ![B]: ![S]: ![N]: ((infix_lseq(const_0,
  to_int1(S)) & infix_ls(to_int1(S), const_8)) => ((infix_lseq(const_0, N)
  & infix_ls(N, const_8)) => (infix_ls(infix_pl(N, prefix_mn(to_int1(S))),
  const_0) => ~ nth2(lsl_modulo2(B, S), N))))).

fof(lsl2, axiom, ![B]: ![S]: ((infix_lseq(const_0, to_int1(S))
  & infix_ls(to_int1(S), const_8)) => ((lsr2(lsl_modulo2(B, S), S) = S)
  => (lsl2(B, S) = lsl_modulo2(B, S))))).

fof(lsr_unsigned2, axiom, $true).

fof(asr_signed2, axiom, ![A]: ![N]: ((infix_lseq(const_0, to_int1(N))
  & infix_ls(to_int1(N), const_8)) => (to_int1(asr2(A, N)) = div1(to_int1(A),
  power2(to_int1(N)))))).

fof(lsl_modulo2, axiom, ![A]: ![N]: ((infix_lseq(const_0, to_int1(N))
  & infix_ls(to_int1(N), const_8)) => (to_int1(lsl_modulo2(A,
  N)) = infix_pl(prefix_mn(const_128), mod1(infix_pl(infix_as(to_int1(A),
  power2(to_int1(N))), prefix_mn(prefix_mn(const_128))),
  infix_pl(infix_pl(const_127, prefix_mn(prefix_mn(const_128))),
  const_1)))))).

fof(to_int_def1, axiom, ![A]: (to_int1(A) = infix_pl($ite_t(nth2(A, const_0),
  const_1, const_0), infix_pl($ite_t(nth2(A, const_1), const_2, const_0),
  infix_pl($ite_t(nth2(A, const_2), const_4, const_0),
  infix_pl($ite_t(nth2(A, const_3), const_8, const_0),
  infix_pl($ite_t(nth2(A, const_4), const_16, const_0),
  infix_pl($ite_t(nth2(A, const_5), const_32, const_0),
  infix_pl($ite_t(nth2(A, const_6), const_64, const_0), $ite_t(nth2(A,
  const_7), prefix_mn(const_128), const_0)))))))))).

fof(cast_modulo_sort, axiom, ![X]: (sort(t1,
  cast_modulo(X)) = cast_modulo(X))).

fof(cast_modulo, axiom, ![A]:
  (cast_modulo(A) = of_int1(infix_pl(prefix_mn(const_128),
  mod1(infix_pl(to_int2(A), prefix_mn(prefix_mn(const_128))),
  infix_pl(infix_pl(const_127, prefix_mn(prefix_mn(const_128))),
  const_1)))))).

fof(mk_ref_sort, axiom, ![A]: ![X]: (sort(ref(A), mk_ref(A, X)) = mk_ref(A,
  X))).

fof(contents_sort, axiom, ![A]: ![X]: (sort(A, contents(A, X)) = contents(A,
  X))).

fof(contents_def, axiom, ![A]: ![U]: (contents(A, mk_ref(A, U)) = sort(A,
  U))).

fof(ref_inversion, axiom, ![A]: ![U]: (sort(ref(A), U) = mk_ref(A,
  contents(A, U)))).

fof(null_sort, axiom, ![T]: (sort(pointer(T), null(T)) = null(T))).

fof(null_sort1, axiom, (sort(pointer(voidP), null1) = null1)).

fof(sub_pointer_sort, axiom, ![T]: ![X, X1]: (sort(int, sub_pointer(T, X,
  X1)) = sub_pointer(T, X, X1))).

fof(shift_sort, axiom, ![T]: ![X, X1]: (sort(pointer(T), shift(T, X,
  X1)) = shift(T, X, X1))).

fof(sub_pointer_def, axiom, ![T]: ![A]: ![I, J]: (sub_pointer(T, shift(T, A,
  I), shift(T, A, J)) = infix_pl(I, prefix_mn(J)))).

fof(shift_def1, axiom, ![T]: ![A]: ![I]: ![J]: (shift(T, shift(T, A, I),
  J) = shift(T, A, infix_pl(I, J)))).

fof(shift_def2, axiom, ![T]: ![A]: (shift(T, A, const_0) = sort(pointer(T),
  A))).

fof(same_block_def, axiom, ![T]: ![A, B]: ((same_block(T, A, B) => ?[I]:
  ((sort(int, I) = I) & (sort(pointer(T), A) = shift(T, B, I)))) & (?[I]:
  (A = shift(T, B, I)) => same_block(T, A, B)))).

fof(sub_pointer_shift, axiom, ![T]: ![P, Q]: (same_block(T, P, Q)
  => (sort(pointer(T), P) = shift(T, Q, sub_pointer(T, P, Q))))).

fof(sub_pointer_self, axiom, ![T]: ![P]: (sub_pointer(T, P, P) = const_0)).

fof(sub_pointer_zero, axiom, ![T]: ![P, Q]: (same_block(T, P, Q)
  => ((sub_pointer(T, P, Q) = const_0) => (sort(pointer(T),
  P) = sort(pointer(T), Q))))).

fof(sub_pointer_shift_left, axiom, ![T]: ![P, Q, I]: (same_block(T, P, Q)
  => (sub_pointer(T, shift(T, P, I), Q) = infix_pl(sub_pointer(T, P, Q),
  I)))).

fof(sub_pointer_shift_right, axiom, ![T]: ![P, Q, I]: (same_block(T, P, Q)
  => (sub_pointer(T, P, shift(T, Q, I)) = infix_pl(sub_pointer(T, P, Q),
  prefix_mn(I))))).

fof(sub_pointer_neg, axiom, ![T]: ![P, Q]: (same_block(T, P, Q)
  => (sub_pointer(T, P, Q) = prefix_mn(sub_pointer(T, Q, P))))).

fof(shift_shift, axiom, ![T]: ![P]: ![I, J]: (shift(T, shift(T, P, I),
  J) = shift(T, P, infix_pl(I, J)))).

fof(neq_shift, axiom, ![T]: ![P]: ![I]: ![J]: (~ (I = J) => ~ (shift(T, P,
  I) = shift(T, P, J)))).

fof(same_block_refl, axiom, ![T]: ![P]: same_block(T, P, P)).

fof(same_block_shift, axiom, ![T]: ![P]: ![I]: same_block(T, P, shift(T, P,
  I))).

fof(same_block_symm, axiom, ![T]: ![P]: ![Q]: (same_block(T, P, Q)
  <=> same_block(T, Q, P))).

fof(same_block_trans, axiom, ![T]: ![P]: ![Q]: ![R]: ((same_block(T, P, Q)
  & same_block(T, Q, R)) => same_block(T, P, R))).

fof(same_block_shift_right, axiom, ![T]: ![P]: ![Q]: ![I]: (same_block(T, P,
  Q) => same_block(T, P, shift(T, Q, I)))).

fof(same_block_shift_left, axiom, ![T]: ![P]: ![Q]: ![I]: (same_block(T, Q,
  P) => same_block(T, shift(T, Q, I), P))).

fof(get_sort, axiom, ![A, B]: ![X, X1]: (sort(B, get(B, A, X, X1)) = get(B,
  A, X, X1))).

fof(get_sort1, axiom, ![X, X1]: (sort(tag_id(voidP), get1(X, X1)) = get1(X,
  X1))).

fof(set_sort, axiom, ![A, B]: ![X, X1, X2]: (sort(map(A, B), set(B, A, X, X1,
  X2)) = set(B, A, X, X1, X2))).

fof(select_eq, axiom, ![M]: ![A1, A2]: ![B]: ((A1 = A2)
  => (get1(set(tag_id(voidP), pointer(voidP), M, A1, B),
  A2) = sort(tag_id(voidP), B)))).

fof(select_eq1, axiom, ![A, B]: ![M]: ![A1, A2]: ![B1]: ((A1 = A2) => (get(B,
  A, set(B, A, M, A1, B1), A2) = sort(B, B1)))).

fof(select_neq, axiom, ![M]: ![A1, A2]: ![B]: (~ (sort(pointer(voidP),
  A1) = sort(pointer(voidP), A2)) => (get1(set(tag_id(voidP), pointer(voidP),
  M, A1, B), A2) = get1(M, A2)))).

fof(select_neq1, axiom, ![A, B]: ![M]: ![A1, A2]: ![B1]: (~ (sort(A,
  A1) = sort(A, A2)) => (get(B, A, set(B, A, M, A1, B1), A2) = get(B, A, M,
  A2)))).

fof(int_of_tag_sort, axiom, ![T]: ![X]: (sort(int, int_of_tag(T,
  X)) = int_of_tag(T, X))).

fof(voidp_whole_block_tag, axiom, ![T]: ![P]: ![Q]: (same_block(voidP, P, Q)
  => (get1(T, P) = get1(T, Q)))).

fof(subtag_refl, axiom, ![T]: subtag(T, T)).

fof(subtag_refl1, axiom, ![T]: ![T1]: subtag1(T, T1, T1)).

fof(subtag_parent, axiom, ![T1]: ![T2]: ![T3]: (subtag(T1, T2)
  => (parenttag(voidP, T2, T3) => subtag(T1, T3)))).

fof(subtag_parent1, axiom, ![T]: ![T1]: ![T2]: ![T3]: (subtag1(T, T1, T2)
  => (parenttag(T, T2, T3) => subtag1(T, T1, T3)))).

fof(subtag_antisymmetric, axiom, ![T1, T2]: (subtag(T1, T2) => (subtag(T2,
  T1) => (sort(tag_id(voidP), T1) = sort(tag_id(voidP), T2))))).

fof(subtag_antisymmetric1, axiom, ![T]: ![T1, T2]: (subtag1(T, T1, T2)
  => (subtag1(T, T2, T1) => (sort(tag_id(T), T1) = sort(tag_id(T), T2))))).

fof(bottom_tag_sort, axiom, ![A]: (sort(tag_id(A),
  bottom_tag(A)) = bottom_tag(A))).

fof(bottom_tag, axiom, ![T]: subtag(T, bottom_tag(voidP))).

fof(bottom_tag1, axiom, ![T]: ![T1]: subtag1(T, T1, bottom_tag(T))).

fof(bottom_int, axiom, ![A]: (int_of_tag(A, bottom_tag(A)) = const_0)).

fof(root_subtag, axiom, ![A]: ![B]: ![C]: (parenttag(voidP, A,
  bottom_tag(voidP)) => (parenttag(voidP, B, bottom_tag(voidP)) => (~
  (sort(tag_id(voidP), A) = sort(tag_id(voidP), B)) => (subtag(C, A) => ~
  subtag(C, B)))))).

fof(root_subtag1, axiom, ![T]: ![A]: ![B]: ![C]: (parenttag(T, A,
  bottom_tag(T)) => (parenttag(T, B, bottom_tag(T)) => (~ (sort(tag_id(T),
  A) = sort(tag_id(T), B)) => (subtag1(T, C, A) => ~ subtag1(T, C, B)))))).

fof(voidP_tag_sort, axiom, (sort(tag_id(voidP), voidP_tag) = voidP_tag)).

fof(voidp_int, axiom, (int_of_tag(voidP, voidP_tag) = const_1)).

fof(voidp_parenttag_bottom, axiom, parenttag(voidP, voidP_tag,
  bottom_tag(voidP))).

fof(offset_min_sort, axiom, ![T]: ![X, X1]: (sort(int, offset_min(T, X,
  X1)) = offset_min(T, X, X1))).

fof(offset_max_sort, axiom, ![T]: ![X, X1]: (sort(int, offset_max(T, X,
  X1)) = offset_max(T, X, X1))).

fof(null_pointer, axiom, ![A]: ((offset_max(voidP, A,
  null1) = prefix_mn(const_2)) & (infix_ls(prefix_mn(const_2),
  offset_min(voidP, A, null1)) & (offset_min(voidP, A, null1) = const_0)))).

fof(null_pointer1, axiom, ![T]: ![A]: ((offset_max(T, A,
  null(T)) = prefix_mn(const_2)) & (infix_ls(prefix_mn(const_2),
  offset_min(T, A, null(T))) & (offset_min(T, A, null(T)) = const_0)))).

fof(offset_max_shift, axiom, ![T]: ![A]: ![P]: ![I]: (offset_max(T, A,
  shift(T, P, I)) = infix_pl(offset_max(T, A, P), prefix_mn(I)))).

fof(offset_min_shift, axiom, ![T]: ![A]: ![P]: ![I]: (offset_min(T, A,
  shift(T, P, I)) = infix_pl(offset_min(T, A, P), prefix_mn(I)))).

fof(downcast_sort, axiom, ![T]: ![X, X1, X2]: (sort(pointer(T), downcast(T,
  X, X1, X2)) = downcast(T, X, X1, X2))).

fof(downcast_instanceof, axiom, ![T]: ![P]: ![S]: (subtag(get1(T, P), S)
  => (downcast(voidP, T, P, S) = sort(pointer(voidP), P)))).

fof(downcast_instanceof1, axiom, ![T]: ![T1]: ![P]: ![S]: (subtag1(T,
  get(tag_id(T), pointer(T), T1, P), S) => (downcast(T, T1, P,
  S) = sort(pointer(T), P)))).

fof(downcast_null, axiom, ![T]: ![S]: (downcast(voidP, T, null1,
  S) = null1)).

fof(downcast_null1, axiom, ![T]: ![T1]: ![S]: (downcast(T, T1, null(T),
  S) = null(T))).

fof(charP_tag_sort, axiom, (sort(tag_id(voidP), charP_tag) = charP_tag)).

fof(charp_int, axiom, (int_of_tag(voidP, charP_tag) = const_2)).

fof(charp_is_final, axiom, ![T]: ![P]: (subtag(get1(T, P), charP_tag)
  => (get1(T, P) = charP_tag))).

fof(charp_parenttag_voidp, axiom, parenttag(voidP, charP_tag, voidP_tag)).

fof(alloc_fresh_not_same_block, axiom, ![T]: ![P1]: ![P2]: ![A]:
  ((((offset_max(T, A, P1) = prefix_mn(const_1))
  & (infix_ls(prefix_mn(const_1), offset_min(T, A, P1)) & (offset_min(T, A,
  P1) = const_0))) & ((offset_min(T, A, P2) = const_0) & infix_lseq(const_0,
  offset_max(T, A, P2)))) => ~ same_block(T, P1, P2))).

fof(s_2_0_sort, axiom, (sort(pointer(voidP), s_2_0) = s_2_0)).

fof(c_13_1_sort, axiom, (sort(t2, c_13_1) = c_13_1)).

fof(count_2_sort, axiom, (sort(t, count_2) = count_2)).

fof(voidP_s_2_77_alloc_table_sort, axiom, (sort(alloc_table(voidP),
  voidP_s_2_77_alloc_table) = voidP_s_2_77_alloc_table)).

fof(voidP_s_2_77_tag_table_sort, axiom, (sort(map(pointer(voidP),
  tag_id(voidP)), voidP_s_2_77_tag_table) = voidP_s_2_77_tag_table)).

fof(h, axiom, ((infix_lseq(offset_min(voidP, voidP_s_2_77_alloc_table,
  s_2_0), offset_max(voidP, voidP_s_2_77_alloc_table, s_2_0))
  => (subtag(get1(voidP_s_2_77_tag_table, s_2_0), voidP_tag) & ![I]:
  ((infix_lseq(offset_min(voidP, voidP_s_2_77_alloc_table, s_2_0), I)
  & infix_ls(I, offset_max(voidP, voidP_s_2_77_alloc_table, s_2_0)))
  => subtag(get1(voidP_s_2_77_tag_table, shift(voidP, s_2_0, I)),
  voidP_tag)))) & (subtag(get1(voidP_s_2_77_tag_table, s_2_0), charP_tag)
  & (infix_lseq(const_0, infix_pl(to_int(count_2), prefix_mn(const_1)))
  => (infix_lseq(offset_min(voidP, voidP_s_2_77_alloc_table, downcast(voidP,
  voidP_s_2_77_tag_table, s_2_0, charP_tag)), const_0)
  & infix_gteq(offset_max(voidP, voidP_s_2_77_alloc_table, downcast(voidP,
  voidP_s_2_77_tag_table, s_2_0, charP_tag)), infix_pl(to_int(count_2),
  prefix_mn(const_1)))))))).

fof(wP_parameter_memset, conjecture, (subtag(get1(voidP_s_2_77_tag_table,
  s_2_0), charP_tag) | (s_2_0 = null1))).
