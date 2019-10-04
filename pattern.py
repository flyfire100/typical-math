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


class MetaVariable(ABT):
    def __init__(self, ident, closure=None, name=None):
        self.name = str(ident) if name is None else name
        self.ident = ident
        self.closure = closure if closure is not None else ()
        self._hash = hash(self.name) ^ hash(self.closure) ^ hash(ident)

    def __repr__(self):
        return self.name + ("" if self.closure == () else
                            "[%s]" % "; ".join(str(d)[1:-1] for d in self.closure))

    def __hash__(self):
        return self._hash

    def substitute(self, dict):
        if self in dict:
            return dict[self]
        # TODO: More on substituting away metavars with closure
        return MetaVariable(self.ident, (*self.closure, dict), self.name)

    def __eq__(self, other):
        return isinstance(other, MetaVariable) and self.ident == other.ident and \
               self.closure == other.closure and self.name == other.name


def match(expr: ABT, pattern: ABT) -> dict:
    try:
        if isinstance(pattern, MetaVariable):
            return {pattern: expr}
        elif isinstance(expr, Variable) and isinstance(pattern, Variable):
            return dict()
        elif isinstance(expr, Node) and isinstance(pattern, Node):
            if len(expr.args) != len(pattern.args):
                raise ValueError("Node arguments mismatch.")
            return merge_dicts(*map(match, expr.args, pattern.args))
        elif isinstance(expr, Bind) and isinstance(pattern, Bind):
            return match(expr.expr.substitute(expr.bv, pattern.bv), pattern.expr)
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


def subs_metavariables(expr: ABT, ass: dict) -> ABT:  # The key of ass should be closure-free metavars..?
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
    elif isinstance(expr, Node):
        return Node(expr.name, tuple(subs_metavariables(a, ass) for a in expr.args))
    elif isinstance(expr, Bind):
        return Bind(expr.bv, subs_metavariables(expr.expr, ass))
    else:
        return expr


if __name__ == "__main__":
    pass
