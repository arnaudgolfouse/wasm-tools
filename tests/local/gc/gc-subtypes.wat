;; --enable-gc

(module
  (type $a (func))
  (type $b (sub $a (func)))
  (type $c (sub $b (func)))
  (type $b1 (sub final $a (func)))

  ;; struct, ref types, mutability, nullability
  (type $d (struct))
  (type $e (sub $d (struct (field (mut (ref null $d)))))) ;; width
  (type $f (sub final $e (struct (field (ref $e))))) ;; depth

  ;; func
  (type $g (func (param (ref $e)) (result (ref $e))))
  (type $h (sub $g (func (param (ref $d)) (result (ref $f)))))

  (type $j (func (param (ref $b)) (result (ref $b))))
  (type $k (sub $j (func (param (ref $a)) (result (ref $c)))))

  ;; valid: expanded param/result types are equal to those of the parent
  (type $l (sub $j (func (param (ref $c)) (result (ref $a)))))

  ;; array, val types, ref types, mutability, nullability
  (type $m (array (mut i32)))
  (type $n (sub $m (array i32)))

  (type $o (array i32))
  (type $p (sub $o (array i32)))

  (type $o1 (array i64))
  (type $p1 (sub $o1 (array i64)))

  ;; any refs
  (type $q (array (mut anyref)))
  (type $q0 (sub $q (array (ref any))))

  ;; eq refs
  (type $q1 (sub $q (array (mut eqref))))
  (type $q2 (sub $q1 (array (mut (ref eq)))))
  (type $q3 (sub $q2 (array (ref eq))))

  ;; i31 refs
  (type $r (sub $q (array i31ref)))
  (type $r1 (sub $q1 (array i31ref)))
  (type $s (sub $r (array (ref i31))))
  (type $s1 (sub $q1 (array (ref i31))))
  (type $s2 (sub $q2 (array (ref i31))))

  ;; array refs
  (type $rr (sub $q (array arrayref)))
  (type $rr1 (sub $q1 (array arrayref)))
  (type $ss (sub $rr (array (ref array))))
  (type $ss0 (sub $ss (array (ref $rr))))
  (type $ss1 (sub $q1 (array (ref array))))
  (type (sub $q1 (array (ref $rr))))
  (type $ss2 (sub $q2 (array (ref array))))
  (type (sub $q2 (array (ref $rr))))

  ;; struct refs
  (type $rrr (sub $q (array structref)))
  (type $rrr1 (sub $q1 (array structref)))
  (type $sss (sub $rrr (array (ref struct))))
  (type $sss0 (sub $rrr (array (ref null $d))))
  (type $sss1 (sub $q1 (array (ref struct))))
  (type (sub $q1 (array (ref $d))))
  (type $sss2 (sub $q2 (array (ref struct))))
  (type (sub $q2 (array (ref $d))))

  ;; none refs
  (type $z1 (sub $q (array (mut nullref))))
  (type $z2 (sub $q0 (array (ref none))))
  (type $z3 (sub $z1 (array (mut (ref none)))))
  (type $z4 (sub $z1 (array nullref)))
  (type (sub $q1 (array nullref)))
  (type (sub $r (array nullref)))
  (type (sub $rr (array nullref)))
  (type (sub $rrr (array nullref)))
  (type (sub $q1 (array (ref none))))
  (type (sub $r (array (ref none))))
  (type (sub $rr (array (ref none))))
  (type (sub $rrr (array (ref none))))

  ;; func refs
  (type $t (array (mut funcref)))
  (type $u (sub $t (array (ref null func))))
  (type $v (sub $u (array (ref func))))
  (type $w (sub $v (array (ref $a))))
  (type $x (sub $t (array (ref null $a))))
  (type $y (sub $w (array (ref nofunc))))
  (type $z (sub $x (array nullfuncref)))

  ;; extern refs
  (type $t0 (array (mut externref)))
  (type $u0 (sub $t0 (array (ref null extern))))
  (type $v0 (sub $u0 (array (ref extern))))
  (type $y0 (sub $v0 (array (ref noextern))))
  (type $y01 (sub $u0 (array (ref noextern))))
  (type $z0 (sub $u0 (array nullexternref)))
)
