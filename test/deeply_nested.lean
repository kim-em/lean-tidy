import tidy.tidy

namespace deeply_nested

structure A :=
(z : ℕ)

structure B := 
(a : A)
(aa : a.z = 0)

structure C :=
(a : A)
(b : B)
(ab : a.z = b.a.z)

structure D :=
(a : B)
(b : C)
(ab : a.a.z = b.a.z)

structure E :=
(a : C)
(b : D)
(ab : a.b.a.z = b.b.a.z)

structure F :=
(a : D)
(b : E)
(ab : a.b.b.a.z = b.b.b.a.z)

structure G :=
(a : E)
(b : F)
(ab : a.b.b.b.a.z = b.b.b.b.a.z)

structure H :=
(a : F)
(b : G)
(ab : a.b.b.b.b.a.z = b.b.b.b.b.a.z)

structure I :=
(a : G)
(b : H)
(ab : a.b.b.b.b.b.a.z = b.b.b.b.b.b.a.z)

structure J :=
(a : H)
(b : I)
(ab : a.b.b.b.b.b.b.a.z = b.b.b.b.b.b.b.a.z)

structure K :=
(a : I)
(b : J)
(ab : a.b.b.b.b.b.b.b.a.z = b.b.b.b.b.b.b.b.a.z)

structure L :=
(a : J)
(b : K)
(ab : a.b.b.b.b.b.b.b.b.a.z = b.b.b.b.b.b.b.b.b.a.z)

structure M :=
(a : K)
(b : L)
(ab : a.b.b.b.b.b.b.b.b.b.a.z = b.b.b.b.b.b.b.b.b.b.a.z)

structure N :=
(a : L)
(b : M)
(ab : a.b.b.b.b.b.b.b.b.b.b.a.z = b.b.b.b.b.b.b.b.b.b.b.a.z)

def f : L := by tidy {max_steps:=100000}

#print f
end deeply_nested