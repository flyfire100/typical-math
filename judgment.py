from abt import *


def merge_dicts(*res):
    """Merges two dictionaries and check if they are consistent."""
    ans = dict()  # TODO: maybe more elegant?
    for r in res:
        for k in r:
            if k in ans and ans[k] != r[k]:
                raise ValueError("Inconsistent dictionaries.")
            ans[k] = r[k]
    return ans


def freeze(d: dict) -> tuple:
    return tuple([(k, d[k]) for k in d])


def unfreeze(fd) -> dict:
    return {k: v for k, v in fd}


class MetaVariable(ABT):
    fresh_counter = 0

    def __init__(self, ident, closure=None, name=None):
        self.name = str(ident) if name is None else name
        self.ident = ident
        self.closure = closure if closure is not None else ()
        self._hash = hash(self.name) ^ hash(self.closure) ^ hash(ident)

    def __repr__(self):
        return self.name + ("" if self.closure == () else
                            "[%s]" % "; ".join(repr(d) for d in self.closure))

    def __hash__(self):
        return self._hash

    def substitute(self, dict):
        if self in dict:
            return dict[self]
        # TODO: More on substituting away metavars with closure
        return MetaVariable(self.ident, (*self.closure, freeze(dict)), self.name)

    def __eq__(self, other):
        return isinstance(other, MetaVariable) and self.ident == other.ident and \
               self.closure == other.closure and self.name == other.name


class Judgment(Node):
    """Subclass of Node, used to keep track of input/output type arguments."""
    def __init__(self, name, inputs, outputs):
        super().__init__(name, (*inputs, *outputs))
        self.inputs = tuple(inputs)
        self.outputs = tuple(outputs)
        self._hash ^= hash(self.inputs) ^ hash(self.outputs)
        self._repr = self.name % (*self.inputs, *self.outputs)

    def __repr__(self):
        return self._repr

    def substitute(self, dict):
        return Judgment(self.name, tuple(e.substitute(dict) for e in self.inputs),
                        tuple(e.substitute(dict) for e in self.outputs))

    def __eq__(self, other):
        return isinstance(other, Node) and self.name == other.name and \
               self.inputs == other.inputs and self.outputs == other.outputs


def match(expr: ABT, pattern: ABT) -> dict:
    try:
        if isinstance(pattern, MetaVariable):
            return {pattern: expr}
        elif isinstance(expr, Variable) and isinstance(pattern, Variable):
            return dict()
        elif isinstance(expr, Node) and isinstance(pattern, Node):
            if expr.name != pattern.name:
                raise ValueError("Node name mismatch.")
            elif len(expr.args) != len(pattern.args):
                raise ValueError("Node arguments mismatch.")
            return merge_dicts(*map(match, expr.args, pattern.args))
        elif isinstance(expr, Bind) and isinstance(pattern, Bind):
            return match(expr.expr.substitute({expr.bv: pattern.bv}), pattern.expr)
        else:
            raise ValueError("Node type mismatch.")
    except ValueError as e:
        raise ValueError("Match failed: inconsistent.")


def get_metavariables(expr: ABT) -> frozenset:
    if isinstance(expr, MetaVariable):
        return frozenset({expr})
    elif isinstance(expr, Node):
        return frozenset().union(*(get_metavariables(c) for c in expr.args))
    elif isinstance(expr, Bind):
        return get_metavariables(expr.expr)
    else:
        return frozenset()


def subs_metavariables(expr: ABT, ass: dict):  # TODO: consider making it an object method
    if isinstance(expr, MetaVariable):
        for v in ass:
            if v.closure != ():
                print("[METAV] A metavar with closure is being substituted!")
            if expr.ident == v.ident and expr.name == v.name:
                er = ass[v]
                for vv, ee in expr.closure:
                    er = er.substitute(vv, ee)
                return er
        return expr
    elif isinstance(expr, Judgment):  # Special case of Node; we don't want to lose information
        return Judgment(expr.name, tuple(subs_metavariables(e, ass) for e in expr.inputs),
                        tuple(subs_metavariables(e, ass) for e in expr.outputs))
    elif isinstance(expr, Node):
        return Node(expr.name, tuple(subs_metavariables(a, ass) for a in expr.args))
    elif isinstance(expr, Bind):
        return Bind(expr.bv, subs_metavariables(expr.expr, ass))
    else:
        return expr


class InferenceRule:
    def __init__(self, name, premises, conclusion, condition=None):
        # condition is additional conditions that may be present.
        # This should be a function accepting a dict
        self.name = name
        self.premises = tuple(premises)
        self.conclusion = conclusion
        self.variables = frozenset().union(get_metavariables(conclusion), *map(get_metavariables, premises))
        self.condition = condition \
            if condition is not None else lambda d: True

    def __call__(self, pr, concl):
        return Derivation(self, pr, concl)

    def __repr__(self):
        return self.name

    def with_fresh_metavariables(self):  # TODO: we need to get fresh metavars for Bind too.
        # TODO implement this as object method
        fresh_juice_raw = [(v, MetaVariable((v.ident, InferenceRule.fresh_counter),
                                            v.closure, v.name + "f%d" % InferenceRule.fresh_counter)) for v in self.variables]
        InferenceRule.fresh_counter += 1
        fresh_juice = {a: b for a,b in fresh_juice_raw}
        fresh_juice_inverted = {b: a for a,b in fresh_juice_raw}
        return InferenceRule(self.name, tuple(subs_metavariables(p, fresh_juice) for p in self.premises),
                             subs_metavariables(self.conclusion, fresh_juice),
                             lambda d: self.condition({fresh_juice_inverted[k]: d[k] for k in d}))


class Derivation:
    def __init__(self, rule: InferenceRule, prem, concl: ABT):
        self.rule = rule
        assert all(map(lambda x: isinstance(x, Derivation), prem))
        try:
            prem_match = merge_dicts(*map(match, (p.conclusion for p in prem), rule.premises))
            res_match = match(concl, rule.conclusion)
            subs = merge_dicts(prem_match, res_match)
        except ValueError as e:
            raise ValueError("Inconsistent assignment of metavariables.")
        self.premises = tuple(prem)
        self.conclusion = concl
        self.assignment = subs

    def __repr__(self):
        return "Derivation of %s" % repr(self.conclusion)

    def _pretty(self):
        if len(self.premises) == 0:
            a = ['']
            width = 0
        else:
            derivstrs = [p._pretty() for p in self.premises]
            derivlens = list(map(lambda l: len(l[0]), derivstrs))
            a = []
            while not all(len(i) == 0 for i in derivstrs):
                a.insert(0, '  '.join(i.pop() if len(i) != 0 else " " * derivlens[n]
                                      for n, i in enumerate(derivstrs)))
            width = len(a[-1])
        concl = repr(self.conclusion)
        wc = len(concl)
        total_width = max(width, wc) + 2
        return [ai.center(total_width, ' ') for ai in a] + \
               ['-' * total_width] + [concl.center(total_width, ' ')]

    def pretty(self):
        return '\n'.join(self._pretty())

    # ##### How automatic inference works ##### #
    # We take the known parts in the judgment,
    # and by unification with each inference rules
    # we pick out the ones that result in a
    # consistent unification, and, one-by-one, try
    # to recursively find the expression to fill
    # in the metavariables in the premises. We
    # take the first successful one, and fill in
    # the unknown parts of the conclusion with the
    # now-known knowledge.

    # We *DO* need explicit marking of inputs and outputs!
    # marking that makes unification unecessary.
    # we can't sort out all the mess unify makes..


def infer(judgment: Judgment, rules):
    print("[INFER] Inferring %s." % repr(judgment))
    for rule in rules:  # try each rule
        rule = rule.with_fresh_metavariables()
        print("[INFER] Trying rule %s." % rule)
        if judgment.name != rule.conclusion.name:
            continue
        try:
            assignment = merge_dicts(*(match(k, rule.conclusion.inputs[n]) for n, k in enumerate(judgment.inputs)))
            print("[INFER] Conclusion successfully matched.", assignment)
            prem_deriv = []  # fulfill premises
            alright = True
            for p in rule.premises:
                da = infer(subs_metavariables(p, assignment), rules)
                if da is None:  # fails
                    alright = False
                    break
                d, a = da
                prem_deriv.append(d)
                # Succeeded. We collect the derivation tree and assignments
                try:
                    assignment = merge_dicts(assignment, a)
                except ValueError as v:
                    # print("[INFER] Merge conflict.")  # Debug; need to remove this
                    alright = False
                    break  # merge conflict
            if not alright:
                continue
            conclusion = subs_metavariables(rule.conclusion, assignment)
            concl_assignment = merge_dicts(*(match(cop, judgment.outputs[n]) for n, cop in enumerate(conclusion.outputs)))
            assignment = merge_dicts(assignment, concl_assignment)
            if frozenset().union(*(get_metavariables(oj) for oj in conclusion.outputs)) != frozenset():
                print("[INFER]", assignment)
                print("[INFER]   Unable to fully infer all unknowns.")
                print("[INFER]   Inferring %s." % judgment)
                print("[INFER]   Using rule %s." % rule, conclusion)
                continue
            # at last.. check the additional conditions
            if not rule.condition({v : assignment[v] for v in rule.variables}):
                print("[INFER] Condition not satisfied.")
                continue
            print("[INFER] Success.", {k: assignment[k] for k in get_metavariables(judgment)})
            return rule(tuple(prem_deriv), conclusion), assignment
            # {k: assignment[k] for k in get_metavariables(judgment)}
        except ValueError as v:
            continue
    # by now no rules apply, so fail
    print("[INFER] Failed inferring %s." % judgment)
    return None
