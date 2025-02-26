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
Version: 1.0.2
Date: 02/27/2025
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


    def cnf_to_dnf(cnf, is_base=True):
        if not cnf:
            return []
        
        # Base case: Convert single clause CNF into a sorted list of literals
        if len(cnf) == 1:
            return sorted([list(literal) for literal in cnf[0]])
    
        # Recursive step
        rest_dnf = CNFReducer.cnf_to_dnf(cnf[1:], is_base=False)
    
        # Expand CNF into DNF while avoiding redundancy
        result = []
        minimal_result = set() if is_base else None  # Track minimal terms only at base level
    
        for literal in cnf[0]:
            for clause in rest_dnf:
                new_clause = sorted(set(list(literal) + clause))
    
                if is_base:
                    new_clause_set = frozenset(new_clause)
    
                    # **Skip if it's already covered by a smaller term**
                    if any(existing.issubset(new_clause_set) for existing in minimal_result):
                        continue  
    
                    # **Remove larger clauses that the new one replaces**
                    to_remove = {existing for existing in minimal_result if new_clause_set.issubset(existing)}
                    minimal_result -= to_remove  # Efficiently remove redundant larger terms
    
                    minimal_result.add(new_clause_set)  # Add only minimal term
                else:
                    result.append(new_clause)
    
        # Convert minimal_result back to sorted lists if `is_base=True`
        return [sorted(list(clause)) for clause in minimal_result] if is_base else result


    def is_satisfiable(self):
        """
        Convert a reduced CNF (where each literal is a tuple) to DNF by expanding tuples.
        For literals of length 1, we treat them as scalars.
        """
        for g in self.reduced_cnf:
            if not CNFReducer.is_clause_satisfiable(g):
                return False  # If any group is unsatisfiable, return False
        return True  # All groups are satisfiable

    def is_dnf_clause_satisfiable(dnf_clause):
        if not dnf_clause:
            return False
        plus_set = set([a for a in dnf_clause if a > 0])  # Positive literals
        minus_set = set([-a for a in dnf_clause if a < 0])  # Negative literals

        if not (plus_set & minus_set):
            return True
        else:
            return False
    
    def is_clause_satisfiable(cnf):
        """
        Converts CNF to DNF and checks if at least one clause in the group is satisfiable.
        """
        if not cnf:
            return False  # An empty CNF is trivially unsatisfiable
    
        if len(cnf) == 1:
            
            for dnf_clause in cnf[0]:
                if CNFReducer.is_dnf_clause_satisfiable(dnf_clause):
                    return True
                    
            return False
        # Recursively expand CNF into DNF
        rest_dnf = CNFReducer.cnf_to_dnf(cnf[1:], is_base=False)
        for literal in cnf[0]:
            for clause in rest_dnf:
                # **Create a flat list of literals in the current clause**
                    
                dnf_clause = list(set(list(literal) + clause))
                if CNFReducer.is_dnf_clause_satisfiable(dnf_clause):
                    return True


        return False  # If all clauses contain contradictions, return False

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