CoInductive strm := { hd : nat; tl : strm }.

CoFixpoint seq n := {| hd := n; tl := seq (S n) |}.

Definition test_lazy := Eval lazy in
  let x := seq in
  (hd (x 1), hd (x 5)).

Definition test_vm := Eval vm_compute in
  let x := seq in
  (hd (x 1), hd (x 5)).

Definition test_native := Eval native_compute in
  let x := seq in
  (hd (x 1), hd (x 5)).

Check eq_refl : test_lazy = (1, 5).
Check eq_refl : test_lazy = test_vm.
Check eq_refl : test_lazy = test_native.
