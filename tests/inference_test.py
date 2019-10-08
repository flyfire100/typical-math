from judgment import *

print("##### TEST I #####")
Zero = Node("0", ())
Succ = lambda expr: Node("S", (expr,))
isNat = lambda expr: Judgment("%s nat", (expr,), ())

n = MetaVariable("n")

Onat = InferenceRule("Onat", (), isNat(Zero))
Snat = InferenceRule("Snat", (isNat(n),), isNat(Succ(n)))
# We build derivation trees by hand.
ZeroIsNat = Derivation(Onat, (), isNat(Zero))
OneIsNat = Derivation(Snat, (ZeroIsNat,), isNat(Succ(Zero)))

print(OneIsNat.pretty())

OneIsNat_auto, assignments = infer(isNat(Succ(Zero)), [Onat, Snat])

print(OneIsNat_auto.pretty())

print()
print("##### TEST II #####")
# We redo the stlc system, systematically.

A = MetaVariable("A")
B = MetaVariable("B")
C = MetaVariable("C")
E = MetaVariable("E")
M = MetaVariable("M")
N = MetaVariable("N")

TA = Node("A", ())
TB = Node("B", ())
TC = Node("C", ())

OneType = Node("1", ())
ZeroType = Node("0", ())


def L(x, A, E):  # a more natural way of stating lambda
    return Node("λ", (Bind(x, E), A))


App = lambda a, b: Node("@", (a, b))
To = lambda a, b: Node("->", (a, b))

x = MetaVariable("x")
y = MetaVariable("y")
z = MetaVariable("z")
a = Variable("a")
b = Variable("b")
c = Variable("c")

S_combinator = L(a, To(TA, To(TB, TC)), L(b, To(TA, TB), L(c, TA, App(App(a, c), App(b, c)))))
print(S_combinator)  # This is becoming Lisp....

colon = lambda a, b: Node(":", (a, b))

# -- Contexts
Gamma = MetaVariable("Gamma")
epsilon = Node("*", ())  # Empty context
cons = lambda a, b: Node("::", (a, b))  # reverse cons

# -- lookup
lookup = lambda c, a, b: \
    Judgment("%s |- %s lookup ~> %s", (c, a), (b,))  # lookup
lookup_pop = InferenceRule("POP", (), lookup(cons(Gamma, colon(x, A)), x, A))
lookup_next = InferenceRule("NEXT", (lookup(Gamma, x, A),), lookup(cons(Gamma, colon(y, B)), x, A),
                            lambda d: d[y] != d[x])

inference_rules = [lookup_pop, lookup_next]
simple_lookup = lookup(cons(cons(epsilon, colon(a, OneType)), colon(b, ZeroType)), a, C)
print(infer(simple_lookup, inference_rules)[0].pretty())

# -- synth and check
synth = lambda c, a, b: \
    Judgment("%s |- %s synth ~> %s", (c, a), (b,))
check = lambda c, a, b: \
    Judgment("%s |- check %s : %s", (c, a, b), ())

SV = InferenceRule("SV", (lookup(Gamma, x, A),), synth(Gamma, x, A), lambda d: isinstance(d[x], Variable))
SL = InferenceRule("SL", (synth(cons(Gamma, colon(x, A)), E, B),), synth(Gamma, L(x, A, E), To(A, B)),
                   lambda d: isinstance(d[x], Variable))
SA = InferenceRule("SA", (synth(Gamma, M, To(A, B)), check(Gamma, N, A)), synth(Gamma, App(M, N), B),
                   lambda d: isinstance(d[x], Variable))

CV = InferenceRule("CV", (lookup(Gamma, x, A),), check(Gamma, x, A),
                   lambda d: isinstance(d[x], Variable))
CL = InferenceRule("CL", (check(cons(Gamma, colon(x, A)), E, B),), check(Gamma, L(x, A, E), To(A, B)),
                   lambda d: isinstance(d[x], Variable))
CA = InferenceRule("CA", (synth(Gamma, N, A), check(Gamma, M, To(A, B))), check(Gamma, App(M, N), B),
                   lambda d: isinstance(d[x], Variable))

inference_rules.extend([SV, SL, SA, CV, CL, CA])
print(infer(synth(epsilon, S_combinator, M), inference_rules)[0].pretty())
