import * as backtalk from './backtalk.js';

class SolverForTest extends backtalk.Solver {
    propagateInstantiationFor(constraint) {
        return constraint.enforceArcConsistency();
    }
}

function equals(a1, a2) {
    if (!Array.isArray(a1) || !Array.isArray(a2)) {
        throw new Error("Arguments to function equals(a1, a2) must be arrays.");
    }

    if (a1.length !== a2.length) {
        return false;
    }

    for (var i=0; i<a1.length; i++) {
        if (Array.isArray(a1[i]) && Array.isArray(a2[i])) {
            if (equals(a1[i], a2[i])) {
                continue;
            } else {
                return false;
            }
        } else {
            if (a1[i] !== a2[i]) {
                return false;
            }
        }
    }

    return true;
}

var self = {};

describe('backtalk', function() {
    beforeEach(function() {
        self = {
            assert: function(cond, msg) {
                if (!cond) {
                    throw new Error(msg || "Assertion error");
                }
            }
        };
    });

    describe('backtalk.Variable', function() {
        beforeEach(function() {
            self.variable = backtalk.Variable.labelFromTo('x', 1, 3);
        });

        it("ConnectionBetweenValuesToExploreAndCurrentValue", function () {
            self.variable.currentValue = 2;
            self.variable.valuesToExplore = [];
            self.assert(self.variable.valuesToExplore.length === 0);
            self.assert(!self.variable.currentValue);
        });
    });

    describe('backtalk.BinaryConstraintTest', function() {
        beforeEach(function () {
            self.variable1 = backtalk.Variable.labelFromTo('v1', 1, 10);
            self.variable2 = backtalk.Variable.labelFromTo('v2', 2, 12);
            self.constraint = new backtalk.EqualityConstraint(self.variable1, self.variable2);
        });
        it("testDomainWipedOut", function() {
            self.assert(!self.constraint.domainWipedOut());
            self.variable1.valuesToExplore = [];
            self.assert(self.constraint.domainWipedOut());
            self.variable1.reset();
            self.variable2.valuesToExplore = [];
            self.assert(self.constraint.domainWipedOut());
        });
        it("testReferencesAfterVariableRemoval", function() {
            var expectedConstraints, expectedVariables, newVariable;
            newVariable = new backtalk.Variable('x', 1, 2);
            self.constraint.variableA = newVariable;
            expectedConstraints = [self.constraint];
            expectedVariables = [self.variable2, newVariable];
            self.assert(self.variable1.constraints.length === 0);
            self.assert(equals(self.variable2.constraints, expectedConstraints));
            self.assert(self.constraint.variables().filter(function (v) {
                return expectedVariables.indexOf(v) >= 0;
            }).length === expectedVariables.length);
        });
    });

    describe('backtalk.CSPTest', function() {
        beforeEach(function() {
            self.variable1 = backtalk.Variable.labelFromTo('v1', 1, 10);
            self.variable2 = backtalk.Variable.labelFromTo('v2', 2, 12);
            self.constraint = new backtalk.EqualityConstraint(self.variable1, self.variable2);
            self.variable3 = backtalk.Variable.labelFromTo('v3', 5, 8);
            self.variable4 = backtalk.Variable.labelFromTo('v4', 3, 6);
            self.constraint2 = new backtalk.EqualityConstraint(self.variable3, self.variable4);
            self.csp = backtalk.CSP.labelVariables('cspTest', [self.variable1, self.variable2]);
            self.csp.addVariable(self.variable3);
            self.csp.addVariable(self.variable4);
            self.solver = new SolverForTest(self.csp)
            self.solver.reset();
        });

        it("testAllSolutionsOnATrivialCSP", function() {
            var expectedSolution,solutions;
            self.variable1.domain = [3]
            self.variable2.domain = [3]
            self.variable3.domain = [6]
            self.variable4.domain = [6]
            solutions = self.solver.allSolutions();
            self.assert(solutions.length === 1)
            self.assert(equals(solutions[0].keys, [self.variable1, self.variable2, self.variable3, self.variable4]));
            self.assert(solutions[0][self.variable1.uuid] === 3)
            self.assert(solutions[0][self.variable2.uuid] === 3)
            self.assert(solutions[0][self.variable3.uuid] === 6)
            self.assert(solutions[0][self.variable4.uuid] === 6)
        });

        // it("testAllSolutions", function() {
        //     var solutions, v1, v2, v3, v4;
        //     solutions = self.solver.allSolutions();
        //     self.assert(self.solver.explorationFinished());
        //     self.assert(solutions.length === 18)
        //     solutions.each(function (s) {
        //         v1 = s[self.variable1.uuid]
        //         v2 = s[self.variable2.uuid]
        //         self.assert(v1 == v2)
        //         v3 = s[self.variable3.uuid]
        //         v4 = s[self.variable4.uuid]
        //         self.assert(v3 == v4)
        //     }.bind(this));
        // });
    });
});
