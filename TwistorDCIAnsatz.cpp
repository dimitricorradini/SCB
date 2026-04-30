// TwistorDCIAnsatz.cpp — C++ rewrite
// Compile: g++ -O3 -std=c++17 -o ansatz TwistorDCIAnsatz.cpp
// Usage: ./ansatz <nPoints> <nLoops>

#include <iostream>
#include <vector>
#include <array>
#include <set>
#include <map>
#include <algorithm>
#include <numeric>
#include <random>
#include <cmath>
#include <functional>
#include <chrono>
#include <cassert>
#include <unordered_map>
#include <unordered_set>

using namespace std;

// ================================================================
//  4x4 Determinant
// ================================================================
using Vec4 = array<double, 4>;
using Bracket = array<int, 4>;

double det4(const Vec4& a, const Vec4& b, const Vec4& c, const Vec4& d) {
    double m00 = b[1]*(c[2]*d[3]-c[3]*d[2]) - b[2]*(c[1]*d[3]-c[3]*d[1]) + b[3]*(c[1]*d[2]-c[2]*d[1]);
    double m01 = b[0]*(c[2]*d[3]-c[3]*d[2]) - b[2]*(c[0]*d[3]-c[3]*d[0]) + b[3]*(c[0]*d[2]-c[2]*d[0]);
    double m02 = b[0]*(c[1]*d[3]-c[3]*d[1]) - b[1]*(c[0]*d[3]-c[3]*d[0]) + b[3]*(c[0]*d[1]-c[1]*d[0]);
    double m03 = b[0]*(c[1]*d[2]-c[2]*d[1]) - b[1]*(c[0]*d[2]-c[2]*d[0]) + b[2]*(c[0]*d[1]-c[1]*d[0]);
    return a[0]*m00 - a[1]*m01 + a[2]*m02 - a[3]*m03;
}

// ================================================================
//  Planarity Testing (edge count + biconnected components)
// ================================================================
struct Graph {
    int n;
    vector<vector<int>> adj;
    Graph(int _n) : n(_n), adj(_n) {}
    void addEdge(int u, int v) { adj[u].push_back(v); adj[v].push_back(u); }
    
    bool isConnected() const {
        if (n == 0) return true;
        vector<bool> vis(n, false);
        vector<int> q = {0};
        vis[0] = true;
        for (int i = 0; i < (int)q.size(); i++) {
            for (int w : adj[q[i]]) {
                if (!vis[w]) { vis[w] = true; q.push_back(w); }
            }
        }
        return (int)q.size() == n;
    }
    
    bool isPlanar() const {
        if (n <= 4) return true;
        int m = 0;
        for (int i = 0; i < n; i++) m += adj[i].size();
        m /= 2;
        if (n >= 3 && m > 3 * n - 6) return false;
        
        // DMP planarity test
        // Build simple adjacency (remove multi-edges for algorithm)
        vector<set<int>> sadj(n);
        for (int u = 0; u < n; u++)
            for (int v : adj[u]) if (u != v) sadj[u].insert(v);
        
        // Recount edges
        m = 0;
        for (int i = 0; i < n; i++) m += sadj[i].size();
        m /= 2;
        if (n >= 3 && m > 3 * n - 6) return false;
        
        // Find connected components, test each
        vector<bool> globalVis(n, false);
        for (int start = 0; start < n; start++) {
            if (globalVis[start]) continue;
            vector<int> comp;
            {
                vector<int> q = {start};
                globalVis[start] = true;
                for (int i = 0; i < (int)q.size(); i++) {
                    comp.push_back(q[i]);
                    for (int w : sadj[q[i]]) 
                        if (!globalVis[w]) { globalVis[w] = true; q.push_back(w); }
                }
            }
            if (comp.size() <= 4) continue;
            
            int cn = comp.size();
            int ce = 0;
            for (int v : comp) ce += sadj[v].size();
            ce /= 2;
            if (cn >= 3 && ce > 3*cn - 6) return false;
            if (ce <= cn + 2) continue; // tree or near-tree, always planar
            
            // Map to local indices
            map<int,int> toLocal;
            for (int i = 0; i < cn; i++) toLocal[comp[i]] = i;
            vector<set<int>> ladj(cn);
            for (int v : comp)
                for (int w : sadj[v])
                    if (toLocal.count(w)) ladj[toLocal[v]].insert(toLocal[w]);
            
            if (!dmpTest(cn, ladj)) return false;
        }
        return true;
    }
    
    // DMP planarity test for a connected graph
    bool dmpTest(int cn, vector<set<int>>& ladj) const {
        int ce = 0;
        for (int i = 0; i < cn; i++) ce += ladj[i].size();
        ce /= 2;
        if (cn >= 3 && ce > 3*cn - 6) return false;
        if (cn <= 4) return true;
        
        // Step 1: find a cycle via DFS
        vector<int> par(cn, -1), depth(cn, -1);
        int cs = -1, cend = -1;
        
        function<bool(int)> findCyc = [&](int v) -> bool {
            for (int w : ladj[v]) {
                if (w == par[v]) continue;
                if (depth[w] >= 0) { cs = w; cend = v; return true; }
                par[w] = v; depth[w] = depth[v] + 1;
                if (findCyc(w)) return true;
            }
            return false;
        };
        depth[0] = 0;
        if (!findCyc(0)) return true; // no cycle = tree = planar
        
        vector<int> cycle;
        for (int v = cend; v != cs; v = par[v]) cycle.push_back(v);
        cycle.push_back(cs);
        reverse(cycle.begin(), cycle.end());
        int nc = cycle.size();
        
        // Step 2: init embedding with cycle
        vector<vector<int>> rot(cn); // rotation system
        set<int> embedded(cycle.begin(), cycle.end());
        set<pair<int,int>> embeddedEdges;
        
        for (int i = 0; i < nc; i++) {
            int v = cycle[i], prev = cycle[(i-1+nc)%nc], next = cycle[(i+1)%nc];
            rot[v] = {next, prev}; // clockwise: next, prev
            embeddedEdges.insert({min(v,prev), max(v,prev)});
        }
        
        // Collect all edges
        set<pair<int,int>> allEdges;
        for (int u = 0; u < cn; u++)
            for (int v : ladj[u]) if (u < v) allEdges.insert({u, v});
        
        // Remaining edges
        set<pair<int,int>> remaining;
        for (auto& e : allEdges)
            if (!embeddedEdges.count(e)) remaining.insert(e);
        
        // Step 3: DMP iteration
        int maxIter = ce + 10;
        while (!remaining.empty() && maxIter-- > 0) {
            // Trace faces
            auto faces = traceFaces(cn, rot, embedded);
            
            // Find fragments
            // Type A: edges between two embedded vertices
            // Type B: connected components of non-embedded vertices + attachments
            
            struct Frag {
                set<int> innerVerts;
                set<int> attachments;
                set<pair<int,int>> edges;
            };
            vector<Frag> frags;
            
            // Type A
            set<pair<int,int>> typeAEdges;
            for (auto& [u,v] : remaining)
                if (embedded.count(u) && embedded.count(v)) {
                    Frag f; f.attachments = {u, v}; f.edges = {{u,v}};
                    frags.push_back(f);
                    typeAEdges.insert({u,v});
                }
            
            // Type B
            set<int> unembedded;
            for (auto& [u,v] : remaining) {
                if (!embedded.count(u)) unembedded.insert(u);
                if (!embedded.count(v)) unembedded.insert(v);
            }
            
            set<int> fragVis;
            for (int s : unembedded) {
                if (fragVis.count(s)) continue;
                Frag f;
                vector<int> q = {s};
                fragVis.insert(s);
                while (!q.empty()) {
                    int v = q.back(); q.pop_back();
                    f.innerVerts.insert(v);
                    for (int w : ladj[v]) {
                        if (embedded.count(w)) {
                            f.attachments.insert(w);
                            f.edges.insert({min(v,w), max(v,w)});
                        } else if (!fragVis.count(w)) {
                            fragVis.insert(w);
                            q.push_back(w);
                            f.edges.insert({min(v,w), max(v,w)});
                        }
                    }
                }
                if (!f.attachments.empty()) frags.push_back(f);
            }
            
            if (frags.empty()) break;
            
            // For each fragment, find admissible faces
            int bestFrag = -1, bestFace = -1, minAdm = cn + 1;
            
            for (int fi = 0; fi < (int)frags.size(); fi++) {
                auto& f = frags[fi];
                int adm = 0, lastFace = -1;
                
                for (int fj = 0; fj < (int)faces.size(); fj++) {
                    set<int> fverts(faces[fj].begin(), faces[fj].end());
                    bool ok = true;
                    for (int a : f.attachments)
                        if (!fverts.count(a)) { ok = false; break; }
                    if (ok) { adm++; lastFace = fj; }
                }
                
                if (adm == 0) return false; // NOT PLANAR
                if (adm < minAdm) { minAdm = adm; bestFrag = fi; bestFace = lastFace; }
            }
            
            // Embed bestFrag in bestFace
            auto& f = frags[bestFrag];
            auto& face = faces[bestFace];
            int flen = face.size();
            
            if (f.innerVerts.empty()) {
                // Type A: edge between two embedded vertices
                auto it = f.edges.begin();
                int u = it->first, v = it->second;
                
                // Find positions in face
                int pu = -1, pv = -1;
                for (int i = 0; i < flen; i++) {
                    if (face[i] == u) pu = i;
                    if (face[i] == v) pv = i;
                }
                
                int prevU = face[(pu - 1 + flen) % flen];
                int prevV = face[(pv - 1 + flen) % flen];
                
                // Insert v after prevU in u's rotation
                auto& ru = rot[u];
                auto itu = find(ru.begin(), ru.end(), prevU);
                ru.insert(itu + 1, v);
                
                // Insert u after prevV in v's rotation
                auto& rv = rot[v];
                auto itv = find(rv.begin(), rv.end(), prevV);
                rv.insert(itv + 1, u);
                
                remaining.erase({min(u,v), max(u,v)});
            } else {
                // Type B: find path from attachment to attachment through fragment
                vector<int> atts(f.attachments.begin(), f.attachments.end());
                
                // BFS from atts[0] through inner vertices to find another attachment
                int src = atts[0];
                map<int, int> prev;
                vector<int> bfsq = {src};
                prev[src] = -1;
                int dst = -1;
                
                for (int i = 0; i < (int)bfsq.size() && dst == -1; i++) {
                    int v = bfsq[i];
                    for (int w : ladj[v]) {
                        if (prev.count(w)) continue;
                        if (w == src) continue;
                        if (f.innerVerts.count(w)) {
                            // Inner vertex: always visit
                            prev[w] = v; bfsq.push_back(w);
                        } else if (f.attachments.count(w) && f.innerVerts.count(v)) {
                            // Attachment: only reachable from inner vertex
                            prev[w] = v; dst = w; break;
                        }
                    }
                }
                
                if (dst == -1) {
                    // Only one attachment — add a single edge to the first inner vertex
                    int inner = -1;
                    for (int w : ladj[src])
                        if (f.innerVerts.count(w)) { inner = w; break; }
                    if (inner == -1) return false;
                    
                    int pu = -1;
                    for (int i = 0; i < flen; i++) if (face[i] == src) { pu = i; break; }
                    int prevS = face[(pu - 1 + flen) % flen];
                    
                    auto& rs = rot[src];
                    auto its = find(rs.begin(), rs.end(), prevS);
                    rs.insert(its + 1, inner);
                    rot[inner] = {src};
                    embedded.insert(inner);
                    remaining.erase({min(src,inner), max(src,inner)});
                    continue;
                }
                
                // Extract path
                vector<int> path;
                for (int v = dst; v != -1; v = prev[v]) path.push_back(v);
                reverse(path.begin(), path.end());
                
                // Find face positions
                int pu = -1, pv = -1;
                for (int i = 0; i < flen; i++) {
                    if (face[i] == path.front()) pu = i;
                    if (face[i] == path.back()) pv = i;
                }
                
                int prevU = face[(pu - 1 + flen) % flen];
                int prevV = face[(pv - 1 + flen) % flen];
                
                // Insert first inner vertex after prevU in src's rotation
                {
                    auto& rs = rot[path[0]];
                    auto its = find(rs.begin(), rs.end(), prevU);
                    rs.insert(its + 1, path[1]);
                }
                
                // Insert last inner vertex after prevV in dst's rotation
                {
                    auto& rd = rot[path.back()];
                    auto itd = find(rd.begin(), rd.end(), prevV);
                    rd.insert(itd + 1, path[path.size()-2]);
                }
                
                // Set up rotations for inner path vertices
                for (int i = 1; i < (int)path.size() - 1; i++) {
                    rot[path[i]] = {path[i-1], path[i+1]};
                    embedded.insert(path[i]);
                }
                
                // Remove path edges from remaining
                for (int i = 0; i < (int)path.size() - 1; i++) {
                    int a = path[i], b = path[i+1];
                    remaining.erase({min(a,b), max(a,b)});
                }
            }
        }
        if (!remaining.empty()) return false; // didn't finish
        return true;
    }
    
    // Trace all faces from current rotation system
    vector<vector<int>> traceFaces(int cn, const vector<vector<int>>& rot,
                                    const set<int>& embedded) const {
        // Build next-edge map
        map<pair<int,int>, int> nxt;
        for (int v : embedded) {
            int d = rot[v].size();
            if (d == 0) continue;
            for (int i = 0; i < d; i++)
                nxt[{v, rot[v][i]}] = rot[v][(i + 1) % d];
        }
        
        set<pair<int,int>> visited;
        vector<vector<int>> faces;
        
        for (int u : embedded) {
            for (int v : rot[u]) {
                if (visited.count({u, v})) continue;
                vector<int> face;
                int cu = u, cv = v;
                bool ok = true;
                int limit = 2 * cn + 10;
                while (!visited.count({cu, cv}) && limit-- > 0) {
                    visited.insert({cu, cv});
                    face.push_back(cu);
                    if (nxt.find({cv, cu}) == nxt.end()) { ok = false; break; }
                    int next = nxt[{cv, cu}];
                    cu = cv; cv = next;
                }
                if (ok && !face.empty()) faces.push_back(face);
            }
        }
        return faces;
    }
};

// ================================================================
//  Twistor index encoding
// ================================================================
// Twistors: Z[1]..Z[n] -> indices 0..n-1 (external)
//           A[l], B[l] -> nExt + 2*l, nExt + 2*l+1

int nExt, nLoops, nTwistors;

int zIdx(int i) { return i - 1; }  // Z[i] -> 0-based
int aIdx(int l) { return nExt + 2 * (l - 1); }     // A[l] -> index
int bIdx(int l) { return nExt + 2 * (l - 1) + 1; } // B[l] -> index
bool isExt(int i) { return i < nExt; }
int loopOf(int i) { return (i - nExt) / 2; }
bool isA(int i) { return i >= nExt && (i - nExt) % 2 == 0; }

// ================================================================
//  "Element" = external point or loop pair (graph vertex)
// ================================================================
// Element encoding for graph:
//   0..nExt-1 : external points p[1]..p[nExt]
//   nExt..nExt+nLoops-1 : loop pairs

// A propagator is a pair of elements
using Prop = pair<int, int>;

// After graph check, convert element to twistor pair:
//   external point i -> {Z[i+1], Z[(i+1)%nExt + 1]} = {zIdx(i+1), zIdx(i%nExt+1+1)}
//   Simpler: point i (0-based) -> twistors {i, (i+1)%nExt}
//   loop pair l -> {aIdx(l+1), bIdx(l+1)} = {nExt+2*l, nExt+2*l+1}

pair<int,int> elemToTwistors(int elem) {
    if (elem < nExt) return {elem, (elem + 1) % nExt};
    else {
        int l = elem - nExt;
        return {nExt + 2*l, nExt + 2*l + 1};
    }
}

// ================================================================
//  Symmetry Group
// ================================================================
struct GroupElem { vector<int> perm; /* twistor index permutation */ };

Bracket applyGroup(const GroupElem& g, const Bracket& b) {
    Bracket r = {g.perm[b[0]], g.perm[b[1]], g.perm[b[2]], g.perm[b[3]]};
    sort(r.begin(), r.end());
    return r;
}

struct Integrand {
    vector<Bracket> num, den;
    bool operator<(const Integrand& o) const { return tie(num,den) < tie(o.num,o.den); }
    bool operator==(const Integrand& o) const { return num==o.num && den==o.den; }
};

Integrand applyGroup(const GroupElem& g, const Integrand& integ) {
    Integrand r;
    for (auto& b : integ.num) r.num.push_back(applyGroup(g, b));
    for (auto& b : integ.den) r.den.push_back(applyGroup(g, b));
    sort(r.num.begin(), r.num.end());
    sort(r.den.begin(), r.den.end());
    return r;
}

Integrand canonicalize(const Integrand& integ, const vector<GroupElem>& group) {
    Integrand best = applyGroup(group[0], integ);
    for (size_t i = 1; i < group.size(); i++) {
        Integrand img = applyGroup(group[i], integ);
        if (img < best) best = img;
    }
    return best;
}

vector<GroupElem> buildGroup() {
    // Dihedral on externals × loop permutations
    // Acting on TWISTOR indices
    vector<GroupElem> result;
    
    // Dihedral: rotations + reflections
    vector<vector<int>> dihPerms;
    for (int k = 0; k < nExt; k++) {
        vector<int> p(nTwistors);
        for (int i = 0; i < nExt; i++) p[i] = (i + k) % nExt;
        for (int i = nExt; i < nTwistors; i++) p[i] = i;
        dihPerms.push_back(p);
    }
    // Mirror: Mathematica Z[i] -> Z[Mod[2-i,n]+1], 0-indexed: i -> (1-i+nExt)%nExt
    for (int k = 0; k < nExt; k++) {
        vector<int> p(nTwistors);
        for (int i = 0; i < nExt; i++) {
            int mir = ((1 - i) % nExt + nExt) % nExt;
            p[i] = (mir + k) % nExt;
        }
        for (int i = nExt; i < nTwistors; i++) p[i] = i;
        dihPerms.push_back(p);
    }
    sort(dihPerms.begin(), dihPerms.end());
    dihPerms.erase(unique(dihPerms.begin(), dihPerms.end()), dihPerms.end());
    
    // Loop permutations
    vector<int> loopOrder(nLoops);
    iota(loopOrder.begin(), loopOrder.end(), 0);
    vector<vector<int>> loopPerms;
    do { loopPerms.push_back(loopOrder); } while (next_permutation(loopOrder.begin(), loopOrder.end()));
    
    for (auto& dp : dihPerms) {
        for (auto& lp : loopPerms) {
            GroupElem g; g.perm = dp;
            for (int l = 0; l < nLoops; l++) {
                g.perm[nExt + 2*l] = nExt + 2*lp[l];
                g.perm[nExt + 2*l + 1] = nExt + 2*lp[l] + 1;
            }
            result.push_back(g);
        }
    }
    sort(result.begin(), result.end(), [](auto& a, auto& b){ return a.perm < b.perm; });
    result.erase(unique(result.begin(), result.end(), [](auto& a, auto& b){ return a.perm == b.perm; }), result.end());
    return result;
}

// ================================================================
//  Valid bracket check
// ================================================================
bool validBracketQ(const Bracket& br) {
    set<int> s(br.begin(), br.end());
    if ((int)s.size() < 4) return false;
    vector<int> internals;
    for (int idx : br) if (!isExt(idx)) internals.push_back(idx);
    if (internals.size() == 0) return true;
    if (internals.size() == 2) {
        int a = min(internals[0], internals[1]), b = max(internals[0], internals[1]);
        for (int l = 0; l < nLoops; l++) if (a == nExt+2*l && b == nExt+2*l+1) return true;
        return false;
    }
    if (internals.size() == 4) {
        sort(internals.begin(), internals.end());
        for (int l1 = 0; l1 < nLoops; l1++)
            for (int l2 = l1; l2 < nLoops; l2++) {
                vector<int> exp = {nExt+2*l1, nExt+2*l1+1, nExt+2*l2, nExt+2*l2+1};
                sort(exp.begin(), exp.end());
                if (internals == exp) return true;
            }
        return false;
    }
    return false;
}

// ================================================================
//  Numerator partition generation
// ================================================================
void genPartitions(
    vector<pair<int,int>>& tally, // {index, count}
    const vector<Bracket>& denomBr,
    vector<Bracket>& current,
    vector<vector<Bracket>>& results)
{
    int total = 0;
    for (auto& [idx, cnt] : tally) total += cnt;
    if (total == 0) { results.push_back(current); return; }
    if (total < 4) return;
    
    // Get DISTINCT elements with positive count (matching Mathematica's elems)
    vector<int> elems;
    for (auto& [idx, cnt] : tally) if (cnt > 0) elems.push_back(idx);
    if (elems.empty()) return;
    
    int firstElem = elems[0];
    int nElems = elems.size();
    
    // Generate all 4-subsets of elems containing firstElem as smallest
    // (Mathematica: Select[Subsets[elems, {4}], #[[1]] === First[elems] &])
    for (int j = 1; j < nElems; j++) {
        for (int k = j + 1; k < nElems; k++) {
            for (int l = k + 1; l < nElems; l++) {
                Bracket br = {firstElem, elems[j], elems[k], elems[l]};
                sort(br.begin(), br.end());
                
                if (!validBracketQ(br)) continue;
                
                // Check counts: each element in br must have count >= 1
                auto newTally = tally;
                bool ok = true;
                for (int idx : br) {
                    bool found = false;
                    for (auto& [tidx, tcnt] : newTally)
                        if (tidx == idx && tcnt > 0) { tcnt--; found = true; break; }
                    if (!found) { ok = false; break; }
                }
                if (!ok) continue;
                
                current.push_back(br);
                genPartitions(newTally, denomBr, current, results);
                current.pop_back();
            }
        }
    }
}

// ================================================================
//  Gaussian elimination for matrix rank
// ================================================================
int matRank(vector<vector<double>>& M) {
    int m = M.size(); if (m == 0) return 0;
    int n = M[0].size(), rank = 0;
    for (int col = 0; col < n && rank < m; col++) {
        int pivot = -1; double best = 1e-10;
        for (int r = rank; r < m; r++) if (abs(M[r][col]) > best) { best = abs(M[r][col]); pivot = r; }
        if (pivot < 0) continue;
        swap(M[rank], M[pivot]);
        double inv = 1.0 / M[rank][col];
        for (int j = col; j < n; j++) M[rank][j] *= inv;
        for (int r = 0; r < m; r++) {
            if (r == rank || abs(M[r][col]) < 1e-14) continue;
            double f = M[r][col];
            for (int j = col; j < n; j++) M[r][j] -= f * M[rank][j];
        }
        rank++;
    }
    return rank;
}

// ================================================================
//  Main
// ================================================================
int main(int argc, char* argv[]) {
    if (argc != 3) { cerr << "Usage: ansatz <nPoints> <nLoops>\n"; return 1; }
    nExt = atoi(argv[1]); nLoops = atoi(argv[2]);
    nTwistors = nExt + 2 * nLoops;
    int nElems = nExt + nLoops; // graph vertices (ext points + loop pairs)
    
    auto t0 = chrono::steady_clock::now();
    cerr << "TwistorDCIAnsatz[" << nExt << ", " << nLoops << "]\n";
    
    // ---- Symmetry group ----
    auto fullGroup = buildGroup();
    cerr << "Symmetry group: " << fullGroup.size() << " elements\n";
    
    // ---- Enumerate possible propagators ----
    // Elements: 0..nExt-1 = external points, nExt..nExt+nLoops-1 = loop pairs
    vector<Prop> possibleProps;
    // Loop-loop
    for (int l1 = nExt; l1 < nElems; l1++)
        for (int l2 = l1 + 1; l2 < nElems; l2++)
            possibleProps.push_back({l1, l2});
    // Loop-external
    for (int l = nExt; l < nElems; l++)
        for (int i = 0; i < nExt; i++)
            possibleProps.push_back({min(l,i), max(l,i)});
    
    int nPoss = possibleProps.size();
    cerr << "Possible propagators: " << nPoss << "\n";
    
    // ---- Enumerate subsets satisfying degree constraints ----
    cerr << "Enumerating subsets (" << (1LL << nPoss) << " total)...\n";
    
    // For each element, which props involve it
    vector<vector<int>> elemProps(nElems);
    for (int p = 0; p < nPoss; p++) {
        elemProps[possibleProps[p].first].push_back(p);
        elemProps[possibleProps[p].second].push_back(p);
    }
    
    vector<vector<int>> validSubsets;
    long long total = 1LL << nPoss;
    
    for (long long mask = 0; mask < total; mask++) {
        // Quick degree check
        bool ok = true;
        for (int l = nExt; l < nElems; l++) {
            int cnt = 0;
            for (int p : elemProps[l]) if (mask & (1LL << p)) cnt++;
            if (cnt < 4) { ok = false; break; }
        }
        if (!ok) continue;
        for (int i = 0; i < nExt; i++) {
            int cnt = 0;
            for (int p : elemProps[i]) if (mask & (1LL << p)) cnt++;
            if (cnt < 1) { ok = false; break; }
        }
        if (!ok) continue;
        
        vector<int> sel;
        for (int p = 0; p < nPoss; p++) if (mask & (1LL << p)) sel.push_back(p);
        validSubsets.push_back(sel);
    }
    cerr << "  Valid subsets: " << validSubsets.size() << "\n";
    
    // ---- Planarity + connectivity ----
    cerr << "Checking planarity & connectivity...\n";
    
    // For each valid subset, build graph and check
    // Graph: nElems vertices + 1 star vertex + external cycle
    vector<vector<int>> planarSubsets;
    
    for (auto& sel : validSubsets) {
        // Count edge multiplicities
        map<pair<int,int>, int> edgeMult;
        // External cycle
        for (int i = 0; i < nExt; i++) {
            int j = (i + 1) % nExt;
            edgeMult[{min(i,j), max(i,j)}]++;
        }
        // Star vertex
        int starV = nElems;
        for (int i = 0; i < nExt; i++) edgeMult[{i, starV}]++;
        // Propagators
        for (int p : sel) {
            auto [u, v] = possibleProps[p];
            edgeMult[{min(u,v), max(u,v)}]++;
        }
        
        // Build simple graph (split multi-edges)
        int nV = nElems + 1;
        int nextV = nV;
        vector<pair<int,int>> edges;
        for (auto& [e, cnt] : edgeMult) {
            edges.push_back(e);
            for (int i = 1; i < cnt; i++) {
                edges.push_back({e.first, nextV});
                edges.push_back({nextV, e.second});
                nextV++;
            }
        }
        
        Graph g(nextV);
        for (auto& [u, v] : edges) g.addEdge(u, v);
        
        if (g.isConnected() && g.isPlanar()) {
            planarSubsets.push_back(sel);
        }
    }
    cerr << "  Planar connected: " << planarSubsets.size() << "\n";
    
    // ---- Convert to twistor-space brackets ----
    // Each element -> pair of twistors
    // Prop {elem1, elem2} -> bracket Det[{tw1a, tw1b, tw2a, tw2b}]
    
    struct Topology {
        vector<Bracket> denomBrackets;
        vector<pair<int,int>> twistorPairs; // for each prop, the two twistor pairs
    };
    
    vector<Topology> topologies;
    for (auto& sel : planarSubsets) {
        Topology topo;
        for (int p : sel) {
            auto [e1, e2] = possibleProps[p];
            auto [a1, b1] = elemToTwistors(e1);
            auto [a2, b2] = elemToTwistors(e2);
            Bracket br = {a1, b1, a2, b2};
            sort(br.begin(), br.end());
            topo.denomBrackets.push_back(br);
        }
        sort(topo.denomBrackets.begin(), topo.denomBrackets.end());
        topologies.push_back(topo);
    }
    
    // ---- Numerator index tallies ----
    cerr << "Computing numerator tallies...\n";
    
    // For each topology, compute how many times each twistor index appears
    // in the denominator, then determine numerator indices
    struct TopoData {
        vector<Bracket> denomBr;
        vector<pair<int,int>> tally; // {twistor_index, count_in_numerator}
    };
    
    vector<TopoData> topoData;
    for (auto& topo : topologies) {
        map<int, int> denomCount;
        for (auto& br : topo.denomBrackets)
            for (int idx : br) denomCount[idx]++;
        
        vector<pair<int,int>> tally;
        // Loop indices: need (count - 4) copies per A/B
        for (int l = 0; l < nLoops; l++) {
            int a = nExt + 2*l, b = nExt + 2*l + 1;
            // Count how many brackets contain this loop pair
            int pairCount = 0;
            for (auto& br : topo.denomBrackets) {
                bool hasA = false, hasB = false;
                for (int idx : br) { if (idx==a) hasA=true; if (idx==b) hasB=true; }
                if (hasA && hasB) pairCount++;
            }
            int extra = pairCount - 4;
            if (extra > 0) { tally.push_back({a, extra}); tally.push_back({b, extra}); }
        }
        // External indices: count appearances
        for (int i = 0; i < nExt; i++) {
            if (denomCount.count(i) && denomCount[i] > 0)
                tally.push_back({i, denomCount[i]});
        }
        
        topoData.push_back({topo.denomBrackets, tally});
    }
    
    // ---- Generate numerator partitions + on-the-fly orbit quotient ----
    cerr << "Generating numerators + orbit-quotienting on the fly...\n";
    
    auto hashBracket = [](const Bracket& b) -> size_t {
        size_t h = 0;
        for (int i = 0; i < 4; i++) h = h * 131 + b[i];
        return h;
    };
    auto hashInteg = [&](const Integrand& integ) -> size_t {
        size_t h = 0;
        for (auto& b : integ.num) h ^= hashBracket(b) + 0x9e3779b9 + (h << 6) + (h >> 2);
        h ^= 0xdeadbeef;
        for (auto& b : integ.den) h ^= hashBracket(b) + 0x9e3779b9 + (h << 6) + (h >> 2);
        return h;
    };
    auto canonHash = [&](const Integrand& integ) -> size_t {
        size_t best = hashInteg(applyGroup(fullGroup[0], integ));
        for (size_t i = 1; i < fullGroup.size(); i++) {
            size_t h = hashInteg(applyGroup(fullGroup[i], integ));
            best = min(best, h);
        }
        return best;
    };
    
    unordered_map<size_t, int> seen;
    vector<Integrand> orbitReps;
    long long totalGenerated = 0;
    
    for (int rep = 0; rep < (int)topoData.size(); rep++) {
        if (rep % 10 == 0 || rep == (int)topoData.size()-1)
            cerr << "  Topo " << rep << "/" << topoData.size() 
                 << "  total=" << totalGenerated
                 << "  reps=" << orbitReps.size() << "\r" << flush;
        
        auto& td = topoData[rep];
        vector<vector<Bracket>> partitions;
        vector<Bracket> current;
        genPartitions(td.tally, td.denomBr, current, partitions);
        
        for (auto& numBr : partitions) {
            totalGenerated++;
            
            // Simplify: cancel matching brackets
            multiset<Bracket> denSet(td.denomBr.begin(), td.denomBr.end());
            vector<Bracket> remNum;
            for (auto& b : numBr) {
                auto it = denSet.find(b);
                if (it != denSet.end()) denSet.erase(it);
                else remNum.push_back(b);
            }
            vector<Bracket> remDen(denSet.begin(), denSet.end());
            sort(remNum.begin(), remNum.end());
            sort(remDen.begin(), remDen.end());
            
            Integrand integ = {remNum, remDen};
            size_t h = canonHash(integ);
            if (!seen.count(h)) {
                seen[h] = orbitReps.size();
                orbitReps.push_back(integ);
            }
        }
    }
    cerr << "\n  Total generated: " << totalGenerated << "\n";
    cerr << "  Orbit representatives: " << orbitReps.size() << "\n";
    
    // ---- Numerical rank on orbit-summed integrands ----
    // Optimized: precompute bracket lookup for group-rotated kinematics
    cerr << "Numerical rank computation on orbit-summed integrands...\n";
    mt19937 rng(42);
    uniform_real_distribution<double> dist(-2.0, 2.0);
    
    auto randKin = [&]() -> vector<Vec4> {
        vector<Vec4> tw(nTwistors);
        for (auto& v : tw) for (auto& x : v) x = dist(rng);
        return tw;
    };
    
    // Precompute inverse group actions (for twistor permutation)
    vector<vector<int>> groupInv(fullGroup.size(), vector<int>(nTwistors));
    for (int g = 0; g < (int)fullGroup.size(); g++) {
        for (int i = 0; i < nTwistors; i++)
            groupInv[g][i] = fullGroup[g].perm[i];
    }
    // Note: f^g(tw) = f(tw_g) where tw_g[i] = tw[g.perm[i]]
    
    // Enumerate all brackets that appear in any orbit rep
    set<Bracket> allBrSet;
    for (auto& rep : orbitReps) {
        for (auto& b : rep.num) allBrSet.insert(b);
        for (auto& b : rep.den) allBrSet.insert(b);
    }
    vector<Bracket> allBrackets(allBrSet.begin(), allBrSet.end());
    map<Bracket, int> brIdx;
    for (int i = 0; i < (int)allBrackets.size(); i++) brIdx[allBrackets[i]] = i;
    int nBr = allBrackets.size();
    cerr << "  Unique brackets in orbit reps: " << nBr << "\n";
    
    // Convert orbit reps to index form for fast evaluation
    struct FastInteg {
        vector<int> numIdx, denIdx;
    };
    vector<FastInteg> fastReps(orbitReps.size());
    for (int i = 0; i < (int)orbitReps.size(); i++) {
        for (auto& b : orbitReps[i].num) fastReps[i].numIdx.push_back(brIdx[b]);
        for (auto& b : orbitReps[i].den) fastReps[i].denIdx.push_back(brIdx[b]);
    }
    
    int nReps = orbitReps.size();
    int nKin = 8000;
    
    cerr << "  " << nReps << " orbit reps, " << nKin << " kin points\n";
    
    // Build matrix: rows = orbit reps, cols = kin points
    vector<vector<double>> matT(nReps, vector<double>(nKin));
    int nGrp = fullGroup.size();
    
    for (int k = 0; k < nKin; k++) {
        if (k % 10 == 0) cerr << "    " << k << "/" << nKin << "\r" << flush;
        auto tw = randKin();
        
        // Precompute bracket values at all group-rotated kinematics
        // brCache[g][b] = value of bracket b at g-rotated tw
        vector<vector<double>> brCache(nGrp, vector<double>(nBr));
        for (int g = 0; g < nGrp; g++) {
            // tw_g[i] = tw[g.perm[i]]
            for (int b = 0; b < nBr; b++) {
                brCache[g][b] = det4(
                    tw[groupInv[g][allBrackets[b][0]]],
                    tw[groupInv[g][allBrackets[b][1]]],
                    tw[groupInv[g][allBrackets[b][2]]],
                    tw[groupInv[g][allBrackets[b][3]]]);
            }
        }
        
        // Evaluate all orbit sums using cached brackets
        for (int j = 0; j < nReps; j++) {
            double sum = 0;
            for (int g = 0; g < nGrp; g++) {
                double n = 1, d = 1;
                for (int idx : fastReps[j].numIdx) n *= brCache[g][idx];
                for (int idx : fastReps[j].denIdx) d *= brCache[g][idx];
                sum += n / d;
            }
            matT[j][k] = sum;
        }
    }
    cerr << "\n";
    
    // Incremental rank
    vector<int> indep;
    vector<vector<double>> basis;
    vector<int> pivotCol;
    
    for (int i = 0; i < nReps; i++) {
        if (i % 500 == 0) cerr << "  " << i << "/" << nReps << " found " << indep.size() << "\r" << flush;
        
        vector<double> row = matT[i];
        for (int b = 0; b < (int)basis.size(); b++) {
            double f = row[pivotCol[b]];
            if (abs(f) < 1e-12) continue;
            for (int j = 0; j < nKin; j++) row[j] -= f * basis[b][j];
        }
        
        // Relative pivot threshold
        double rowNorm = 0;
        for (int j = 0; j < nKin; j++) rowNorm = max(rowNorm, abs(matT[i][j]));
        
        int piv = -1;
        double thresh = max(1e-5 * rowNorm, 1e-14);
        double best = thresh;
        for (int j = 0; j < nKin; j++) {
            if (abs(row[j]) > best) { best = abs(row[j]); piv = j; }
        }
        
        if (piv >= 0) {
            double inv = 1.0 / row[piv];
            for (int j = 0; j < nKin; j++) row[j] *= inv;
            basis.push_back(row);
            pivotCol.push_back(piv);
            indep.push_back(i);
        }
    }
    cerr << "\n  Independent orbit reps (greedy): " << indep.size() << "\n";
    
    // Verify rank by full Gaussian elimination on selected rows
    cerr << "  Verifying rank with fresh kinematics...\n";
    int nVerify = indep.size() + 20;
    vector<vector<double>> verifyMat(indep.size(), vector<double>(nVerify));
    for (int k = 0; k < nVerify; k++) {
        auto tw = randKin();
        // Precompute bracket cache for all group rotations
        vector<vector<double>> brCache(nGrp, vector<double>(nBr));
        for (int g = 0; g < nGrp; g++)
            for (int b = 0; b < nBr; b++)
                brCache[g][b] = det4(
                    tw[groupInv[g][allBrackets[b][0]]],
                    tw[groupInv[g][allBrackets[b][1]]],
                    tw[groupInv[g][allBrackets[b][2]]],
                    tw[groupInv[g][allBrackets[b][3]]]);
        for (int ji = 0; ji < (int)indep.size(); ji++) {
            int j = indep[ji];
            double sum = 0;
            for (int g = 0; g < nGrp; g++) {
                double n = 1, d = 1;
                for (int idx : fastReps[j].numIdx) n *= brCache[g][idx];
                for (int idx : fastReps[j].denIdx) d *= brCache[g][idx];
                sum += n / d;
            }
            verifyMat[ji][k] = sum;
        }
    }
    // Compute rank
    auto verCopy = verifyMat;
    int verRank = 0;
    {
        int m = verCopy.size(), n = verCopy[0].size();
        int rank = 0;
        for (int col = 0; col < n && rank < m; col++) {
            int piv = -1; double best = 1e-10;
            for (int r = rank; r < m; r++)
                if (abs(verCopy[r][col]) > best) { best = abs(verCopy[r][col]); piv = r; }
            if (piv < 0) continue;
            swap(verCopy[rank], verCopy[piv]);
            double inv = 1.0 / verCopy[rank][col];
            for (int j = col; j < n; j++) verCopy[rank][j] *= inv;
            for (int r = 0; r < m; r++) {
                if (r == rank || abs(verCopy[r][col]) < 1e-14) continue;
                double f = verCopy[r][col];
                for (int j = col; j < n; j++) verCopy[r][j] -= f * verCopy[rank][j];
            }
            rank++;
        }
        verRank = rank;
    }
    cerr << "  Verified rank: " << verRank << " (greedy selected: " << indep.size() << ")\n";
    
    if (verRank < (int)indep.size()) {
        cerr << "  Removing " << (indep.size() - verRank) << " spurious integrands...\n";
        // Re-select using the verified matrix
        vector<int> indep2;
        vector<vector<double>> basis2;
        vector<int> pivCol2;
        for (int i = 0; i < (int)indep.size(); i++) {
            vector<double> row = verifyMat[i];
            for (int b = 0; b < (int)basis2.size(); b++) {
                double f = row[pivCol2[b]];
                if (abs(f) < 1e-12) continue;
                for (int j = 0; j < nVerify; j++) row[j] -= f * basis2[b][j];
            }
            int piv = -1; double best = 1e-8;
            for (int j = 0; j < nVerify; j++)
                if (abs(row[j]) > best) { best = abs(row[j]); piv = j; }
            if (piv >= 0) {
                double inv = 1.0 / row[piv];
                for (int j = 0; j < nVerify; j++) row[j] *= inv;
                basis2.push_back(row);
                pivCol2.push_back(piv);
                indep2.push_back(indep[i]);
            }
        }
        indep = indep2;
        cerr << "  After cleanup: " << indep.size() << " independent orbit reps\n";
    }
    
    // Extract independent orbit reps
    vector<Integrand> result;
    for (int idx : indep) result.push_back(orbitReps[idx]);
    
    auto t1 = chrono::steady_clock::now();
    cerr << "══════════════════════════════════\n";
    cerr << "  Done: " << result.size() << " independent integrands\n";
    cerr << "  Time: " << chrono::duration<double>(t1-t0).count() << " s\n";
    cerr << "══════════════════════════════════\n";
    
    // ---- Mathematica output ----
    auto brStr = [](const Bracket& br) -> string {
        string s = "Det[{";
        for (int i = 0; i < 4; i++) {
            if (i) s += ",";
            if (br[i] < nExt) s += "Z[" + to_string(br[i]+1) + "]";
            else if ((br[i]-nExt)%2==0) s += "A[" + to_string((br[i]-nExt)/2+1) + "]";
            else s += "B[" + to_string((br[i]-nExt)/2+1) + "]";
        }
        return s + "}]";
    };
    
    cout << "{\n";
    for (int i = 0; i < (int)result.size(); i++) {
        cout << "C[" << i+1 << "] ";
        for (auto& b : result[i].num) cout << brStr(b) << " ";
        if (!result[i].den.empty()) {
            cout << "/ (";
            for (int j = 0; j < (int)result[i].den.size(); j++) {
                if (j) cout << " ";
                cout << brStr(result[i].den[j]);
            }
            cout << ")";
        }
        if (i+1 < (int)result.size()) cout << ",";
        cout << "\n";
    }
    cout << "}\n";
    
    return 0;
}