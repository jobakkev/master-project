from z3 import *
import timeit


def add_items(m : Int):
    """Creates Z3 Int variables for use as allocation items"""
    items = [Int("a" + str(i)) for i in range(1, m+1)]
    return items

def AllocationBounds(items, n : Int):
    return And([And(items[i] > 0, items[i] <= n) for i in range(len(items))])

def add_valuations(s : Solver, n : Int, m : Int):
    """"""
    value_matrix = [[Int("v" + str(j) + "," + str(i)) for i in range(1, m+1)] for j in range(1,n+1)]
    for agent in value_matrix:
        for agent_item in agent:
            s.add(agent_item >= 1)
    return value_matrix

## Adapted From: https://stackoverflow.com/questions/67043494/max-and-min-of-a-set-of-variables-in-z3py
def SmallestValuedItemInBundleForAgent(items, valuations, bundle_id, agent_id):
  # The first item does not necessarily belong to the bundle, in which case we use the total value of the bundle as a starting point
  min = If(items[0] == bundle_id, valuations[agent_id-1][0], ValueOfBundleForAgent(bundle_id, agent_id, items, valuations))
  for i in range(1, len(items)):
    min = If(items[i] == bundle_id, If(valuations[agent_id-1][i] < min, valuations[agent_id-1][i], min), min)
  return min

def GreatestValuedItemInBundleForAgent(items, valuations, bundle_id, agent_id):
  maximum = 0
  for i in range(len(items)):
    maximum = If(items[i] == bundle_id, If(valuations[agent_id-1][i] > maximum, valuations[agent_id-1][i], maximum), maximum)
  return maximum
## End adapt


def ValueOfBundleForAgent(bundle_id, agent_id, items, valuations):
    return Sum([If(items[i] == bundle_id, valuations[agent_id-1][i], 0) for i in range(len(items))])

def EnvyFree(envee_agent, envied_agent, items, valuations):
    return ValueOfBundleForAgent(envee_agent, envee_agent, items, valuations) >= ValueOfBundleForAgent(envied_agent, envee_agent, items, valuations)

def EnvyFreeUpToOneGood(envee_agent, envied_agent, items, valuations):
    return ValueOfBundleForAgent(envee_agent, envee_agent, items, valuations) >= ValueOfBundleForAgent(envied_agent, envee_agent, items, valuations) - GreatestValuedItemInBundleForAgent(items, valuations, envied_agent, envee_agent)

def EnvyFreeInstance(allocation, valuations, num_agents):
    constraint = And([ 
                        And([
                            EnvyFree(i+1, j+1, allocation, valuations) for i in range(num_agents) if i != j
                        ]) for j in range(num_agents)
                    ])
    return constraint
    
def EnvyFreeUpToOneGoodInstance(allocation, valuations, num_agents):
    constraint = And([ 
                        And([
                            EnvyFreeUpToOneGood(i+1, j+1, allocation, valuations) for i in range(num_agents) if i != j
                        ]) for j in range(num_agents)
                    ])
    return constraint


# def ValuationBoundsCheck(s: Solver, val,  num_agents, num_items):
#     i = Int() # agent index
#     j = Int() # item index
#     return ForAll(i, Implies(And(i >= 0, i < num_agents), And(Length(val[i]) == num_items, 
#                                                              ForAll(j, Implies(And(j>= 0, j < num_items), val[i][j] >= 0)))))

def PathConstraint(items):
    return And([items[i] != items[i+1] for i in range(len(items)-1)])

def setup_solver(n, m, logresults=False):
    """Sets up and runs a Z3 solver to check for a fair allocation instance with n agents and m items that does not admit EF1"""
    solver = Solver()
    items = add_items(m)
    valuations = add_valuations(solver, n, m)
    #print(GreatestValuedItemInBundleForAgent(items, valuations, 1, 2))
    solver.add(ForAll(items, Implies(AllocationBounds(items, n), Not(EnvyFreeUpToOneGoodInstance(items, valuations, n)))))
    #print(EnvyFreeUpToOneGoodInstance(items, valuations, n))
    if logresults:
        print("Running solver...")
        result = solver.check()
        print("Instance is " + ("Satisfiable" if result==sat else "Unsatisfiable" if result== unsat else "Unknown"))
        if result == sat:
            print("Producing model:")
            m = solver.model()
            print(m.eval(GreatestValuedItemInBundleForAgent([2,1], valuations, 1, 2)))
            print(f"Value matrix:")
            model_values = [[m[valuations[j][i]] for i in range(len(valuations[j]))] for j in range(len(valuations))]
            for i, agent in enumerate(model_values):
                print(f"Agent {i+1}:", end='')
                for item in agent:
                    print(f" {item}", end='')
                print()
            print("Item assignments:")
            model_allocation = [m[items[i]] for i in range(len(items))]
            print(model_allocation)
    else:
        solver.check()

def setup_solver_path(n, m, logresults=False):
    """Sets up and runs a Z3 solver to check for a fair allocation instance with n agents and m items that does not admit EF1.
    This version further adds conflicting item constraints with a path graph, such that two items of neighbouring index cannot be
    allocated to the same agent"""
    solver = Solver()
    items = add_items(m)
    valuations = add_valuations(solver, n, m)
    solver.add(ForAll(items, Implies(And(AllocationBounds(items, n), PathConstraint(items)), Not(EnvyFreeUpToOneGoodInstance(items, valuations, n)))))
    if logresults:
        print("Running solver...")
        result = solver.check()
        print("Instance is " + ("Satisfiable" if result==sat else "Unsatisfiable" if result== unsat else "Unknown"))
        if result == sat:
            print("Producing model:")
            m = solver.model()
            print(m.eval(GreatestValuedItemInBundleForAgent([2,1], valuations, 1, 2)))
            print(f"Value matrix:")
            model_values = [[m[valuations[j][i]] for i in range(len(valuations[j]))] for j in range(len(valuations))]
            for i, agent in enumerate(model_values):
                print(f"Agent {i+1}:", end='')
                for item in agent:
                    print(f" {item}", end='')
                print()
            print("Item assignments:")
            model_allocation = [m[items[i]] for i in range(len(items))]
            print(model_allocation)
    else:
        solver.check()

def benchmark():
    print(timeit.timeit(stmt="setup_solver(2,2)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver(2,4)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver(2,6)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver(2,8)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver(2,10)", number=1, globals=globals()))

def benchmark_path():
    print(timeit.timeit(stmt="setup_solver_path(2,2)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver_path(2,4)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver_path(2,6)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver_path(2,8)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver_path(2,10)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver_path(2,50)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver_path(2,100)", number=1, globals=globals()))

def benchmark_both():
    print("Without paths:")
    print(timeit.timeit(stmt="setup_solver(3,2)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver(3,3)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver(3,4)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver(3,5)", number=1, globals=globals()))
    #print(timeit.timeit(stmt="setup_solver(3,6)", number=1, globals=globals()))
    print("With paths:")
    print(timeit.timeit(stmt="setup_solver_path(3,2)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver_path(3,3)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver_path(3,4)", number=1, globals=globals()))
    print(timeit.timeit(stmt="setup_solver_path(3,5)", number=1, globals=globals()))
    #print(timeit.timeit(stmt="setup_solver_path(3,6)", number=1, globals=globals()))

def main():
    # for i in range(2, 7):
    #     for j in range(1, 7):
    #         setup_solver(i, j, logresults=True)
    #setup_solver(2, 3, logresults=True)       
    # benchmark_path()
    benchmark_both()
    #print(timeit.timeit(stmt="setup_solver_path(4,5)", number=1, globals=globals()))
    #print(timeit.timeit(stmt="setup_solver(4,5)", number=1, globals=globals()))
    

if __name__ == "__main__":
    main()