class BackTalkObject {
    get uuid() {
        return this._uuid || (this._uuid = guid());
    }
}

export class Variable extends BackTalkObject {
    constructor() {
        super();
        this.constraints = [];
        this.valuesToExplore = [];
    }
    addConstraint(cnstr) {
        if (this.constraints.indexOf(cnstr) !== -1) return;
        this.constraints.push(cnstr);
    }
    removeConstraint(cnstr) {
        remove(this.constraints, cnstr);
    }
    nextValue() {
        if (this.currentValue) {
            remove(this.valuesToExplore, this.currentValue);
        }
        var nextValue = this.valuesToExplore[0];
        this.currentValue = nextValue;
        return nextValue;
    }
    resetCurrentValue() {
        this.currentValue = undefined;
    }
    domainWipedOut() {
        return this.valuesToExplore.length === 0
    }
    isInstantiated() {
        return this.currentValue !== undefined && this.currentValue !== null
    }
    filterToReject(filter) {
        this.valuesToExplore = this.valuesToExplore.filter(function(v) {
            return !filter(v);
        });
    }
    filterToSelect(filter) {
        this.valuesToExplore = this.valuesToExplore.filter(filter);
    }
    get valuesToExplore() {
        return this._valuesToExplore;
    }
    set valuesToExplore(ary) {
        if (ary instanceof Set) {
            ary = Array.from(ary.values());
        } else {
            ary = uniq(ary);
        }
        this._valuesToExplore = ary;
        if (this._valuesToExplore.length === 0) {
            this.resetCurrentValue();
        }
    }
    reset() {
        var idx = this.domain.indexOf(this.currentValue);
        if (idx !== -1) {
            // try the current value first...
            var d = this.domain.slice();
            d.splice(idx, 1);
            d = [this.currentValue].concat(d);
            this.valuesToExplore = d
        } else {
            this.valuesToExplore = this.domain;
        }
        this.resetCurrentValue();
    }
    get domain() {
        return this._domain;
    }
    set domain(d) {
        if (d instanceof Set) {
            d = Array.from(d.values());
        } else {
            d = uniq(d);
        }
        this._domain = d;
        this.valuesToExplore = d;
    }

    static labelDomain(l, d) {
        var v = new Variable();
        v.label = l;
        v.domain = d;
        return v;
    }
    static labelFromTo(l, lower, upper) {
        var v = new Variable();
        v.label = l;
        v.domain = range(lower, upper);
        return v;
    }
}

export class Solver extends BackTalkObject {
    allSolutions() {
        this.reset();
        var allSolutions = [];
        while (!this.explorationFinished()) {
            this.exploreCspStep();
            if (this.solutionFound()) {
                var solution = this.solution();
                if (allSolutions.indexOf(solution) === -1) {
                    allSolutions.push(solution);
                }
                this.stepBackward();
            }
        }
        return uniq(allSolutions);
    }
    chooseAPreviousContext() {
        return this.contexts[this.contexts.length - 1];
    }
    chooseAVariable() {
        if (this.backTrackFlag) {
            return this.currentVariable;
        } else {
            return this.variables().find(function (v) {
                return !v.isInstantiated();
            });
        }
    }
    chooseVariableAndValue() {
        this.currentVariable = this.chooseAVariable();
        this.currentVariable.nextValue();
    }
    exploreCspStep() {
        while (!this.domainWipedOut()) {
            this.stepForward();
            if (this.solutionFound()) {
                return this;
            }
        }
        this.stepBackward();
    }
    firstSolution() {
        this.reset();
        while (!(this.solutionFound() || this.explorationFinished())) {
            this.exploreCspStep();
        }
        return this.solution();
    }
    propagateInstantiationFor(constraint) {
        return constraint.filter();
    }
    propagateInstantiationOfCurrentVariable() {
        if (this.currentVariable.currentValue) {
            this.currentVariable.valuesToExplore = [this.currentVariable.currentValue];
        }
        this.sortedConstraintsForPropagation().find(function (constraint) {
            this.propagateInstantiationFor(constraint);
            if (constraint.domainWipedOut()) {
                return true;
            }
        }.bind(this));
    }
    sortedConstraintsForPropagation() {
        return this.currentVariable.constraints;
    }
    stepBackward() {
        if (this.contexts.length === 0) {
            return this;
        } else {
            var ctx = this.chooseAPreviousContext();
            this.restoreContext(ctx);
            this.backTrackFlag = true;
        }
    }
    stepForward() {
        this.chooseVariableAndValue();
        this.saveContext();
        this.propagateInstantiationOfCurrentVariable();
        this.backTrackFlag = false;
    }
    set currentVariable(v) {
        this._currentVariable = v;
        if (!this.firstChosenVariable) {
            this.firstChosenVariable = v;
        }
    }
    get currentVariable() {
        return this._currentVariable;
    }
    solution() {
        if (!this.solutionFound()) {
            return;
        } else {
            return this.variables().reduce(function (solution, v) {
                solution[v.uuid] = v.currentValue;
                solution.keys.push(v);
                return solution;
            }, {keys: []});
        }
    }
    variables() {
        return this.csp.variables;
    }
    domainWipedOut() {
        if (this.currentVariable &&
            this.backTrackFlag &&
            this.currentVariable.valuesToExplore.length === 0) {
            return true;
        } else {
            return this.variables().some(function (v) {
                return v.domainWipedOut();
            });
        }
    }
    explorationFinished() {
        if (!this.firstChosenVariable) {
            return this.variables().some(function (v) {
                return v.domain.length === 0;
            });
        } else {
            return (this.firstChosenVariable === this.currentVariable &&
                    this.firstChosenVariable.valuesToExplore.length === 0);
        }
    }
    solutionFound() {
        if (!this.variables().every(function (v) { return v.isInstantiated() })) {
            return false;
        } else {
            return this.csp.constraints().every(function (c) {
                return c.isSatisfied();
            });
        }
    }
    constructor(csp) {
        super();
        this.csp = csp;
        this.reset();
    }
    reset() {
        this.csp && this.csp.reset();
        this.contexts = [];
        this.currentVariable = undefined;
        this.firstChosenVariable = undefined;
        this.backTrackFlag = false;
    }
    restoreContext(ctx) {
        remove(this.contexts, ctx);
        ctx.restoreInSolver(this);
    }
    saveContext() {
        this.contexts.push(new Context(this));
    }

    static on(csp) {
        var solver = new Solver();
        solver.csp = csp;
        return solver;
    }
}

class Context extends BackTalkObject {
    constructor(solver) {
        super();
        if (solver) {
            this.fromSolver(solver);
        }
    }
    currentValueFor(v) {
        return this.currentValuesDict[v.uuid];
    }
    fromSolver(solver) {
        this.valuesToExploreDict = {keys: []};
        this.currentValuesDict = {keys: []};
        solver.variables().forEach(function (v) {
            this.valuesToExploreDict[v.uuid] = v.valuesToExplore.slice();
            this.valuesToExploreDict.keys.push(v);
            if (v.isInstantiated()) {
                this.currentValuesDict[v.uuid] = v.currentValue;
                this.currentValuesDict.keys.push(v);
            }
        }.bind(this));
        this.currentVariable = solver.currentVariable;
    }
    restoreInSolver(solver) {
        this.valuesToExploreDict.keys.forEach(function (v) {
            v.valuesToExplore = this.valuesToExploreDict[v.uuid];
        }.bind(this));
        this.currentValuesDict.keys.forEach(function (v) {
            v.currentValue = this.currentValuesDict[v.uuid];
        }.bind(this));
        solver.currentVariable = this.currentVariable;
    }
    valuesToExploreFor(v) {
        return this.valuesToExploreDict[v.uuid];
    }

    static fromSolver(solver) {
        return new Context(solver);
    }
}

export class Constraint extends BackTalkObject {
    domainWipedOut() {
        return this.variables().some(function (v) {
            return v.domainWipedOut();
        });
    }
    isInstantiated() {
        return this.variables().every(function (v) {
            return v.isInstantiated();
        });
    }
    filter() {
        this.enforceArcConsistency();
    }
    isNotConsistent() {
        return !this.isConsistent();
    }
    isSatisfied() {
        return this.isInstantiated() && this.isConsistent();
    }
}

export class UnaryConstraint extends Constraint {
    constructor(v) {
        super();
        this.variable = v;
    }
    valuesToExplore() {
        return this.variable.valuesToExplore;
    }
    get variable() {
        return this._variable;
    }
    set variable(v) {
        if (this._variable) {
            this._variable.removeConstraint(this);
        }
        this._variable = v;
        if (v) v.addConstraint(this);
    }
    variables() {
        return [this.variable];
    }
}


export class BinaryConstraint extends Constraint {
    constructor(a, b) {
        super();
        this.variableA = a;
        this.variableB = b;
    }
    valuesToExploreA() {
        return this.variableA.valuesToExplore;
    }
    valuesToExploreB() {
        return this.variableB.valuesToExplore;
    }
    get variableA() {
        return this._variableA;
    }
    set variableA(v) {
        if (this._variableA) {
            this._variableA.removeConstraint(this);
        }
        this._variableA = v;
        v.addConstraint(this);
    }
    get variableB() {
        return this._variableB;
    }
    set variableB(v) {
        if (this._variableB) {
            this._variableB.removeConstraint(this);
        }
        this._variableB = v;
        if (v) v.addConstraint(this);
    }
    variables() {
        return uniq([this.variableA, this.variableB]);
    }
}

export class CSP extends BackTalkObject {
    constructor() {
        super();
        this.variables = [];
    }
    addVariable(v) {
        if (this.variables.indexOf(v) !== -1) return;
        this.variables.push(v);
    }
    constraints() {
        return uniq(flatten(this.variables.map(function(v) {
            return v.constraints;
        })));
    }
    domainWipedOut() {
        return this.variables.some(function (v) {
            return v.domainWipedOut();
        });
    }
    instantiatedConstraints() {
        return this.constraints().filter(function (c) {
            return c.isInstantiated();
        });
    }
    removeVariable(v) {
        remove(this.variables, v);
    }
    reset() {
        this.variables.forEach(function (v) {
            v.reset();
        });
    }

    static labelVariables(l, v) {
        var csp = new CSP();
        csp.label = l;
        csp.variables = v;
        return csp;
    }
}

export class EqualityConstraint extends BinaryConstraint {
    enforceArcConsistency() {
        var valuesToExploreB = this.valuesToExploreB(),
            intersection = this.valuesToExploreA().filter(function (v) {
                return valuesToExploreB.indexOf(v) >= 0;
        });
        this.variableA.valuesToExplore = intersection;
        this.variableB.valuesToExplore = intersection;
    }
    isConsistent() {
        if (this.variableA.currentValue == this.variableB.currentValue) {
            return true;
        }
        try {
            return this.variableA.equals(this.variableB);
        } catch(_) {}
        try {
            return this.variableA.eq(this.variableB);
        } catch(_) {}
        return false;
    }
};

export class InequalityConstraint extends BinaryConstraint {
    enforceArcConsistency() {
        if (this.valuesToExploreA().length > 1 &&
            this.valuesToExploreB().length > 1) {
            return;
        }
        if (this.valuesToExploreA().length === 0) {
            this.variableB.valuesToExplore = [];
            return;
        }
        if (this.valuesToExploreB().length === 0) {
            this.variableA.valuesToExplore = [];
            return;
        }
        var self = this;
        this.variableB.filterToReject(function (value) {
            return without(self.valuesToExploreA(), value).length === 0;
        });
        this.variableA.filterToReject(function (value) {
            return without(self.valuesToExploreB(), value).length === 0;
        });
    }
    isConsistent() {
        var self = this;
        return (this.valuesToExploreA().every(function (value) {
            return without(self.valuesToExploreB(), value).length > 0
        }) && this.valuesToExploreB().every(function (value) {
            return without(self.valuesToExploreA(), value).length > 0
        }));
    }
}

export class FunctionBinaryConstraint extends BinaryConstraint {
    constructor(a, b, func) {
        super(a, b);
        this.func = func;
    }
    enforceArcConsistency() {
        var sizeA = this.valuesToExploreA().length,
            sizeB = this.valuesToExploreB().length,
            self = this,
            previousSizeA, previousSizeB;
        cond();
        while(previousSizeA !== sizeA && previousSizeB !== sizeB) {
            cond();
        }

        function cond() {
            self.variableA.filterToSelect(function (a) {
                return self.valuesToExploreB().some(function (b) {
                    return self.func(a, b);
                });
            });
            self.variableB.filterToSelect(function (b) {
                return self.valuesToExploreA().some(function (a) {
                    return self.func(a, b);
                });
            });
            previousSizeA = sizeA;
            sizeA = self.valuesToExploreA().length;
            previousSizeB = sizeB;
            sizeB = self.valuesToExploreB().length;
        };
    }
    isConsistent() {
        var condA = this.valuesToExploreA().every(function (a) {
                return this.valuesToExploreB().some(function (b) {
                    return this.func(a, b);
                }.bind(this))
            }.bind(this)),
            condB = this.valuesToExploreB().every(function (b) {
                return this.valuesToExploreA().some(function (a) {
                    return this.func(a, b);
                }.bind(this))
            }.bind(this))
        return condA && condB;
    }

}

class FunctionUnaryConstraint extends UnaryConstraint {
    constructor(v, func) {
        super(v);
        this.func = func;
    }
    enforceArcConsistency() {
        this.variable.filterToSelect(function (v) {
            return this.func(v);
        }.bind(this));
    }
    isConsistent() {
        return this.valuesToExplore().every(function (v) {
            return this.func(v);
        }.bind(this));
    }
}

// Helper functions
function range(a, b) {
    var c = [];
    while (a--) {
        c[a] = a + b;
    }
    return c;
};

function guid() {
    function _p8(s) {
        var p = (Math.random().toString(16) + "000000000").substr(2, 8);
        return s ? "-" + p.substr(0,4) + "-" + p.substr(4,4) : p;
    }
    return _p8() + _p8(true) + _p8(true) + _p8();
}

function without(ary, v) {
    return ary.filter(function (ea) {
        return ea !== v
    });
}

function flatten(ary) {
    return [].concat.apply([], ary);
}

function uniq(ary) {
    return ary.filter(function (v, idx, self) {
        return self.indexOf(v) === idx;
    });
}

function remove(ary, element) {
    var index = ary.indexOf(element);
    if (index > -1) {
        ary.splice(index, 1);
    }
}

if (typeof(Set) == 'undefined') {
    window.Set = function() {
        throw 'Set not supported';
    }
}
