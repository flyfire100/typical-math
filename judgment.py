from abt import *
from pattern import *


class InferenceRule:
    def __init__(self, name, premises, conclusion, condition=None):
        # condition is additional conditions that may be present.
        # This should be a function accepting a dict
        self.name = name
        self.premises = tuple(premises)
        self.conclusion = conclusion
        self.variables = merge_dicts(get_metavariables(conclusion), *map(get_metavariables, premises))
        self.condition = condition \
            if condition is not None else lambda d: True

    def __call__(self, pr, concl):
        return Derivation(self, pr, concl)

    def __repr__(self):
        return self.name

    def with_fresh_metavariables(self):
        fresh_juice_raw = [(v, MetaVariable((v.ident,), v.closure, "f" + v.name)) for v in self.variables]
        # Used tuple around the identifier so that idents will not clash
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
    # TODO: marking that makes unification unecessary.
    # TODO: we can't sort out all the mess unify makes..

"""
def infer(judgment, rules):
    print("[INFER] Inferring %s." % repr(judgment))
    for rule in rules:  # try each rule
        rule = rule.with_fresh_metavariables()
        print("[INFER] Trying rule %s." % rule)
        try:
            assignment = unify([(judgment, rule.conclusion)])  # if one rule matches
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
            if not alright: continue
            conclusion = subs_metavariables(judgment, assignment)
            if get_metavariables(conclusion) != dict():
                # or this?? : any(isinstance(e, MetaVariable) for e in full_assignment.items()):
                print("[INFER]", conclusion)
                print("[INFER]   Unable to fully infer all unknowns.")
                print("[INFER]   Inferring %s." % judgment)
                print("[INFER]   Using rule %s." % rule)
                continue
            # at last.. check the additional conditions
            if not rule.condition({v : assignment[v] for v in rule.variables}):
                continue
            return rule(tuple(prem_deriv), conclusion), \
                   {k: assignment[k] for k in get_metavariables(judgment)}
        except ValueError as v:
            continue
    # by now no rules apply, so fail
    print("[INFER] Failed inferring %s." % judgment)
    return None
"""
