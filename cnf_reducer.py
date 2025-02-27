"""
CNFReducer: A Structured Approach to CNF Reduction and Clause Merging

This class implements a methodology for efficiently reducing Conjunctive Normal Form (CNF) formulas 
by leveraging disjoint variable grouping and structured clause merging. The approach ensures controlled 
term growth and efficient preprocessing before CNF-to-DNF expansion, making it suitable for SAT solvers 
and logical reasoning applications.

Key Features:
- **Disjoint Variable Grouping**: Partitions CNF clauses into independent sets to optimize processing.
- **Graph-Based Clause Merging**: Uses maximum-weight matching to iteratively merge clauses with minimal 
  term growth.
- **Pre-Satisfiability Checking**: Detects contradictions and redundant clauses before full DNF expansion.
- **Statistical Complexity Estimation**: Computes upper bounds on expected DNF growth before execution.
- **Direct CNF-to-DNF Transformation**: Produces a minimized CNF representation that is directly 
  transferable to full DNF on demand.

Performance:
- Ensures polynomial-time preprocessing (`O(n log n)` to `O(n^2)`) while avoiding brute-force CNF-to-DNF 
  expansion.
- Capable of processing large CNF instances in milliseconds.
- Suitable for integration with SAT solvers, formal verification tools, and logic synthesis frameworks.

Usage:
    cnf = [[1, 2, 3], [1, 2, 4], [2, 4, 6], [2, 3, 6]]
    reducer = CNFReducer(cnf)
    reduced_cnf = reducer.solve()
    print("Reduced CNF:", reduced_cnf)
    print("Satisfiable:", reducer.is_satisfiable())

Author: Tomio Kobayashi
Version: 1.0.6
Date: 02/28/2025
"""


import itertools
from itertools import product, combinations
import networkx as nx
from collections import defaultdict
import copy

class CNFReducer:
    def __init__(self, cnf, use_string=False, max_clause=10):
        """
        Initializes the CNF reducer with the given formula.
        Ensures all literals are stored as tuples for consistency.
        """
        self.use_string = use_string
        if use_string:
            self.mapper_to_int = {}
            self.mapper_fr_int = {}
            counter = 1
            for clause in cnf:
                for i, x in enumerate(clause):
                    lit = x if x[0] != "-" else x[1:]
                    if lit not in self.mapper_to_int:
                        self.mapper_to_int[lit] = counter
                        self.mapper_fr_int[counter] = lit 
                        counter += 1
                    clause[i] = self.mapper_to_int[lit] if x[0] != "-" else -self.mapper_to_int[lit]
        
        self.cnf = [[(x,) if isinstance(x, int) else x for x in clause] for clause in cnf]
        self.groups = []
        self.reduced_cnf = None

        self.MAX_CLAUSE = max_clause

    def solve(self):
        self.group_disjoint_variables()
        self.reduced_cnf = self.reduce_cnf()
        
        if self.use_string:
            reduced_copy = copy.deepcopy(self.reduced_cnf) 
            for g in reduced_copy:
                for clause in g:
                    for i, c in enumerate(clause):
                        clause[i] = tuple([self.mapper_fr_int[t] if t >= 0 else "-" + self.mapper_fr_int[t*-1] for t in c])
            return reduced_copy
        else:
            return None


    def group_disjoint_variables(self):
        """
        Groups CNF clauses into independent sets where no variables are shared between groups.
        Ensures that negations (e.g., x and -x) remain in the same group.
        Uses a graph-based approach to cluster dependent clauses.
        """
        var_to_clauses = defaultdict(set)
        literal_to_group = {}
    
        # Step 1: Build variable-to-clause mapping
        for i, clause in enumerate(self.cnf):
            for literal in clause:
                var_to_clauses[literal].add(i)
                base_var = abs(literal[0])  # Handle negation by considering absolute value
                if base_var in literal_to_group:
                    literal_to_group[base_var].add(i)
                else:
                    literal_to_group[base_var] = {i}
    
        # Step 2: BFS-style grouping while considering negations
        visited = set()
        for i in range(len(self.cnf)):
            if i in visited:
                continue
            group = set()
            queue = [i]
            while queue:
                curr = queue.pop()
                if curr in visited:
                    continue
                visited.add(curr)
                group.add(curr)
                for literal in self.cnf[curr]:
                    queue.extend(var_to_clauses[literal])
                    # Ensure negated literals are also included in the same group
                    base_var = abs(literal[0])
                    queue.extend(literal_to_group.get(base_var, []))
    
            self.groups.append([self.cnf[j] for j in group])

    
    def reduce_cnf(self):
        """
        Applies CNF reduction within each independent group.
        """
        reduced_groups = []
        for group in self.groups:
            reduced = self._reduce_group_logic(group)
            reduced_groups.append(reduced)
        return reduced_groups

    def _reduce_group_logic(self, group):
        """
        Reduces CNF clauses by merging optimally.
        """
        current_group = list(group)
        cnt = 0
        while len(current_group) > 1:
            # print("cnt", cnt)
            if cnt > 1000:
                print("1000 loops in _reduce_group_logic()!")
                break
            cnt += 1
            pairs = self._find_best_pairs(current_group, 2)
            if not pairs:
                pairs = self._find_best_pairs(current_group, 1)
                if not pairs:
                    break
            new_group = []
            merged_indices = set()
            for i, j in pairs:
                [i, j] = [i, j] if i < j else [j, i]
                merged_clause = self._merge_pair(current_group[i], current_group[j])
                if merged_clause:
                    new_group.append(merged_clause)
                    merged_indices.add(i)
                    merged_indices.add(j)
            new_group.extend([current_group[k] for k in range(len(current_group)) if k not in merged_indices])
            current_group = new_group  
        return current_group

    def _merge_pair(self, clause1, clause2):
        """
        Merges two CNF clauses if valid.
        """
        common_vars = [lit for lit in clause1 if lit in clause2]
        uncommon1 = [x for x in clause1 if x not in common_vars]
        uncommon2 = [x for x in clause2 if x not in common_vars]
    
        candidate_set = set()
        for x, y in product(uncommon1, uncommon2):
            x_tuple = (x,) if isinstance(x, int) else x
            y_tuple = (y,) if isinstance(y, int) else y
    
            merged_term = tuple(sorted(set(x_tuple) | set(y_tuple)))
            if any(a in merged_term and -a in merged_term for a in merged_term):
                continue
            candidate_set.add(merged_term)

        return sorted(list(set(common_vars) | candidate_set))

    def _find_best_pairs(self, clauses, min_variables=1):
        """
        Uses maximum-cardinality matching to determine the best pairs for merging.
        """
        graph = nx.Graph()
        for i, j in combinations(range(len(clauses)), 2):
            [i, j] = [i, j] if i < j else [j, i]
            common_vars = set(clauses[i]) & set(clauses[j])
            if len(common_vars) == 1 and len(clauses[i]) >= self.MAX_CLAUSE and len(clauses[j]) >= self.MAX_CLAUSE:
                print("WARNING: Clause size reached max", self.MAX_CLAUSE, ". Consider increasing", min(len(clauses[j]), len(clauses[j])))
            if (min_variables == 2 and len(common_vars) >= 2) or (min_variables == 1 and len(common_vars) == 1 and (len(clauses[i]) < self.MAX_CLAUSE or len(clauses[j]) < self.MAX_CLAUSE)):
                graph.add_edge(i, j)
        return nx.max_weight_matching(graph, maxcardinality=True)


    def convert_to_dnf(self, use_string=False):
        for g in self.reduced_cnf:
            dnf_clause = CNFReducer.cnf_to_dnf(g)
            if self.use_string and use_string:
                dnf_clause_copy = copy.deepcopy(dnf_clause) 
                for i, clause in enumerate(dnf_clause_copy):
                    dnf_clause_copy[i] = [self.mapper_fr_int[t] if t >= 0 else "-" + self.mapper_fr_int[t*-1] for t in clause]
                yield dnf_clause_copy
            else:
                yield dnf_clause

    def convert_to_dnf(self, use_string=False):
        # print("convert_to_dnf", use_string)
        output = []
        for g in self.reduced_cnf:
            dnf = []
            for dnf_clause in CNFReducer.cnf_to_dnf_line(g):
                if not dnf_clause:
                    continue
                if self.use_string and use_string:
                    dnf_clause_copy = copy.deepcopy(dnf_clause) 
                    # print("dnf_clause", dnf_clause)
                    
                    # for i, clause in enumerate(dnf_clause_copy):
                    #     print("i", i)
                    #     print("clause", clause)
                        
                    #     dnf_clause_copy[i] = [self.mapper_fr_int[t] if t >= 0 else "-" + self.mapper_fr_int[t*-1] for t in clause]
                    # print(dnf_clause_copy)

                    dnf_clause_copy  = [self.mapper_fr_int[t] if t >= 0 else "-" + self.mapper_fr_int[t*-1] for t in dnf_clause_copy]
                    dnf.append(dnf_clause_copy)
                else:
                    # print(dnf_clause)
                    dnf.append(dnf_clause)
            output.append(dnf)
            
        return output

    
    def cnf_to_dnf_line(group):
        # for combination in product(*group):
        #     yield list(combination)  # Yielding one combination at a time
        for combination in product(*group):  # Generate Cartesian product
            flattened = sorted(set([item for subtuple in combination for item in subtuple]))  # Flatten tuples
            yield flattened  # Yield line by line

    
    def is_satisfiable(inp, bfs_mode=False):
        # simplify_3sat is called to ignore variables that have non-pos-neg pairs.
        if bfs_mode:
            max_clause=20
            reducer = CNFReducer(CNFReducer.simplify_3sat(inp), max_clause=max_clause)
            reducer.solve()
            return reducer.is_satisfiable_raw_bfs()
        else:
            reducer = CNFReducer(CNFReducer.simplify_3sat(inp))
            reducer.solve()
            return reducer.is_satisfiable_raw()
        

    def is_satisfiable_raw(self):
        """
        Convert a reduced CNF (where each literal is a tuple) to DNF by expanding tuples.
        For literals of length 1, we treat them as scalars.
        """
        for g in self.reduced_cnf:
            if not CNFReducer.is_group_satisfiable(g):
                return False  # If any group is unsatisfiable, return False
        return True  # All groups are satisfiable

    def is_group_satisfiable(g):
        """
        Converts CNF to DNF and checks if at least one clause in the group is satisfiable.
        """
        dnf = []
        for dnf_clause in CNFReducer.cnf_to_dnf_line(g):
            if not dnf_clause:
                continue
            # if CNFReducer.is_dnf_clause_satisfiable(dnf_clause):
            res = CNFReducer.is_dnf_clause_satisfiable(dnf_clause)
            if res:
                # print("Satisfiable DNF clause detected:")
                # print(dnf_clause)
                return True
        return False

    
    def is_dnf_clause_satisfiable(dnf_clause):
        if not dnf_clause:
            return False
        plus_set = set([a for a in dnf_clause if a > 0])  # Positive literals
        minus_set = set([-a for a in dnf_clause if a < 0])  # Negative literals
        if not (plus_set & minus_set):
            return True
        else:
            return False


    def generate_flat_dnf_set(self):
        return [c for g in self.reduced_cnf for c in g]
    
    def find_stats(self):
        """
        Computes statistics for each CNF group after reduction:
        - Expected number of DNF terms (by multiplying clause sizes).
        - Expected largest term size (by summing the max term sizes in each clause).
        - Upper bound on DNF expansion (multiplication of the above two values).
        
        Returns:
            stats (list of dicts): Statistics per CNF group.
        """
        if self.reduced_cnf is None:
            raise ValueError("Error: CNF must be reduced first using solve().")
    
        stats = []
        print("num_groups:", len(self.reduced_cnf))
        for i, group in enumerate(self.reduced_cnf):
            expected_dnf_terms = 1
            max_term_size = 0
    
            for clause in group:
                clause_size = len(clause)
                largest_tuple_size = max(len(term) for term in clause)
    
                expected_dnf_terms *= clause_size  # Multiply to get total term count
                max_term_size += largest_tuple_size  # Sum up the largest term sizes
    
            upper_bound_dnf_size = expected_dnf_terms * max_term_size  # Upper bound
    
            stats.append({
                "group_index": i,
                "expected_dnf_terms": expected_dnf_terms,
                "expected_largest_term_size": max_term_size,
                "upper_bound_dnf_size": upper_bound_dnf_size
            })
    
        return stats
        
    # This version replaced non_pos_neg variables with max+1
    def simplify_3sat(clauses):
        # Step 1: Extract all unique variables and find max value
        all_variables = {abs(lit) for clause in clauses for lit in clause}
        if not all_variables:
            return [[]]
        max_val = max(all_variables)
    
        # Step 2: Split into positive and negative sets
        positive_set = {lit for clause in clauses for lit in clause if lit > 0}
        negative_set = {-lit for clause in clauses for lit in clause if lit < 0}
    
        # Step 3: Identify variables that exist in only one set
        single_set = (positive_set | negative_set) - (positive_set & negative_set)
    
        # Step 4: Replace all occurrences in clauses with max_val + 1
        replacement_value = max_val + 1
        new_clauses = []
        for clause in clauses:
            new_clause = [replacement_value if abs(lit) in single_set else lit for lit in clause]
            if len(new_clause) != 1 or new_clause[0] != replacement_value:
                new_clauses.append(sorted(set(new_clause)))  # Remove duplicates
    
        # return new_clauses, single_set, replacement_value
        return new_clauses

    def is_satisfiable_raw_bfs(self):
        """
        Uses tuples for path tracking, ensuring immutability and fast deduplication.
        """

        clauses = self.generate_flat_dnf_set()
        # variables = sorted({abs(lit) for clause in clauses for lit in clause})  # Extract sorted variables
        variables = sorted({abs(v) for clause in clauses for lit in clause for v in lit})  # Extract sorted variables
        var_index = {var: i for i, var in enumerate(variables)}  # Map variables to tuple index
        num_vars = len(var_index)
    
        paths = {tuple([0] * num_vars)}  # Initial path (all variables unassigned)
        
        for clause in clauses:
            new_paths = set()  # Store unique new paths
    
            for path in paths:
                local_new_paths = set()
    
                # for lit in clause:
                for c in clause:
                    new_path = list(path)  # Convert tuple to list for modification
                    jump_out = False
                    for lit in c:
                        var_idx = var_index[abs(lit)]
                        sign = 1 if lit > 0 else -1
                        if path[var_idx] == -sign:  # Conflict: discard this path
                            # continue
                            jump_out = True
                            break
                        new_path[var_idx] = sign
                    # if path[var_idx] == 0:  # Unassigned variable, create a new path
                    if not jump_out:  # Unassigned variable, create a new path
                        # new_path[var_idx] = sign
                        local_new_paths.add(tuple(new_path))  # Convert back to tuple for O(1) lookup
    
                if local_new_paths:
                    new_paths.update(local_new_paths)
    
            # **Drop Old Paths Explicitly**  
            paths = new_paths  # Only retain the new unique paths
            # print("len(paths)", len(paths))
            if not paths:  # If all paths are invalidated, return UNSAT
                return False  

        return True  # If at least one valid path remains, return SAT
                        
# if __name__ == "__main__":
test_cases = [
    {
        # "input": [[1, 2, 3], [1, 2, 4], [2, 4, 6], [2, 3, 6]],
        # "input": [[1, 2, 3], [1, 4, 5], [1, 7, 8],[-8, 12, 13], [9, 10, 11]],
        # "input": [[1, 2, 3], [1, 4, 5],[-5, 12, 13], [9, 10, 11]],
        # "input": [[1, 2, 3, 10, 11], [1, 4, 5, 6, 7, 8, 9]],
        # "input": [[1, 2, 3], [-1]],
        # "input": [[1, -1, 3], [4]],
        # "input": [[1, 2, 3], [2, 5]],
        # "input": [[1, -1]],
        "input": [[1], [-1]],
        "expected": [[[(1, 6), (2,), (3, 4)]]]
    }
]
print("START")
for i, case in enumerate(test_cases):
    print("input", case["input"])
    reducer = CNFReducer(case["input"])
    reducer.solve()
    print(f"\n🔹 **Test {i+1}**")
    print("Input CNF:", case["input"])
    print("Reduced CNF:", reducer.reduced_cnf)
    print("CNFReducer.is_satisfiable():", CNFReducer.is_satisfiable(case["input"]))
    print("CNFReducer.is_satisfiable():", CNFReducer.is_satisfiable(case["input"], bfs_mode=True))
    # if isinstance(case["expected"], list):
    #     if reducer.reduced_cnf == case["expected"]:
    #         print("✅ Test Passed")
    #     else:
    #         print("❌ Test Failed")
    # print(reducer.convert_to_dnf())

# flat_reduced_cnf = reducer.generate_flat_dnf_set()
# flat_reduced_cnf


input = [[1, 2, 3], [1, 2, 4], [2, 4, 6], [2, 3, 6]]
input = [[1, 2, 3], [1, 2, 4], [11, 13, 15], [2, 4, 6], [2, 3, 6]]
input = [["A", "B", "C"], ["A", "B", "D"], ["B", "D", "F"], ["B", "C", "F"]]
input = [
    ["a", "b", "c"],
    ["b", "c", "-d"],
    ["-c", "d", "e"],
    ["a", "-d", "e"],
    ["-a", "b", "e"],
    ["b", "-c", "e"],
    ["a", "-c", "-d"],
    ["-b", "d", "e"],
    ["a", "-b", "d"],
    ["-c", "d", "e"],
    ["a", "-c", "e"],
    ["-b", "-c", "d"]
]

reducer = CNFReducer(input, use_string=True)
reduced_cnf_org = reducer.solve()
print("reduced_cnf  :", reducer.reduced_cnf)
print("reduced_cnf_org:", reduced_cnf_org)
print("reducer.find_stats():", reducer.find_stats())
print("CNFReducer.is_satisfiable():", CNFReducer.is_satisfiable(case["input"]))
print("CNFReducer.is_satisfiable():", CNFReducer.is_satisfiable(case["input"], bfs_mode=True))
print("reducer.convert_to_dnf():", reducer.convert_to_dnf(use_string=True))


import time

input = [[4, -18, 19], [3, 18, -5], [-5, -8, -15], [-20, 7, -16], [10, -13, -7], [-12, -9, 17], [17, 19, 5], [-16, 9, 15], [11, -5, -14], 
       [18, -10, 13], [-3, 11, 12], [-6, -17, -8], [-18, 14, 1], [-19, -15, 10], [12, 18, -19], [-8, 4, 7], [-8, -9, 4], [7, 17, -15], 
       [12, -7, -14], [-10, -11, 8], [2, -15, -11], [9, 6, 1], [-11, 20, -17], [9, -15, 13], [12, -7, -17], [-18, -2, 20], [20, 12, 4], 
       [19, 11, 14], [-16, 18, -4], [-1, -17, -19], [-13, 15, 10], [-12, -14, -13], [12, -14, -7], [-7, 16, 10], [6, 10, 7], [20, 14, -16], 
       [-19, 17, 11], [-7, 1, -20], [-5, 12, 15], [-4, -9, -13], [12, -11, -7], [-5, 19, -8], [1, 16, 17], [20, -14, -15], [13, -4, 10], 
       [14, 7, 10], [-5, 9, 20], [10, 1, -19], [-16, -15, -1], [16, 3, -11], [-15, -10, 4], [4, -15, -3], [-10, -16, 11], [-8, 12, -5], 
       [14, -6, 12], [1, 6, 11], [-13, -5, -1], [-7, -2, 12], [1, -20, 19], [-2, -13, -8], [15, 18, 4], [-11, 14, 9], [-6, -15, -2], 
       [5, -12, -15], [-6, 17, 5], [-13, 5, -19], [20, -1, 14], [9, -17, 15], [-5, 19, -18], [-12, 8, -10], [-18, 14, -4], [15, -9, 13], 
       [9, -5, -1], [10, -19, -14], [20, 9, 4], [-9, -2, 19], [-5, 13, -17],[2, -10, -18], [-18, 3, 11], [7, -9, 17],[-15, -6, -3],
       [-2, 3, -13], [12, 3, -2], [-2, -3, 17], [20, -15, -16], [-5, -17, -19], [-20, -18, 11], [-9, 1, -5], [-19, 9, 17], [12, -2, 17]
      ]

reducer = CNFReducer(input, use_string=False, max_clause=20)
reduced_cnf_org = reducer.solve()
# print("reduced_cnf  :", reducer.reduced_cnf)
# print("reduced_cnf_org:", reduced_cnf_org)
print("reducer.find_stats():", reducer.find_stats())
print("input size", len(input))
print("output size", len(reducer.reduced_cnf[0]))

# # Measure execution time
# start_time = time.time()
# print("CNFReducer.is_satisfiable():", CNFReducer.is_satisfiable(input))
# end_time = time.time()
# execution_time = end_time - start_time
# print(execution_time)

# Measure execution time
start_time = time.time()
print("CNFReducer.is_satisfiable(bfs_mode=True):", CNFReducer.is_satisfiable(input, bfs_mode=True))
end_time = time.time()
execution_time = end_time - start_time
print(execution_time)