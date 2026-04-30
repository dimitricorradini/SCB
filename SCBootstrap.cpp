// SCBootstrap.cpp — Soft-collinear bootstrap driver
// Requires: ./ansatz binary (from TwistorDCIAnsatz.cpp)
// Compile: g++ -O3 -std=c++17 -o scboot SCBootstrap.cpp
// Usage: ./scboot <nPoints> <maxLoops>

#include <iostream>
#include <vector>
#include <array>
#include <set>
#include <map>
#include <algorithm>
#include <random>
#include <cmath>
#include <chrono>
#include <fstream>
#include <sstream>
#include <cstdio>
#include <functional>

using namespace std;

using Vec4 = array<double, 4>;
using Bracket = array<int, 4>;

struct Integrand {
    vector<Bracket> num, den;
    bool operator<(const Integrand& o) const { return tie(num,den) < tie(o.num,o.den); }
    bool operator==(const Integrand& o) const { return num==o.num && den==o.den; }
};

struct GroupElem { vector<int> perm; };

// ================================================================
//  Core numerical functions
// ================================================================

double det4(const Vec4& a, const Vec4& b, const Vec4& c, const Vec4& d) {
    double m00 = b[1]*(c[2]*d[3]-c[3]*d[2]) - b[2]*(c[1]*d[3]-c[3]*d[1]) + b[3]*(c[1]*d[2]-c[2]*d[1]);
    double m01 = b[0]*(c[2]*d[3]-c[3]*d[2]) - b[2]*(c[0]*d[3]-c[3]*d[0]) + b[3]*(c[0]*d[2]-c[2]*d[0]);
    double m02 = b[0]*(c[1]*d[3]-c[3]*d[1]) - b[1]*(c[0]*d[3]-c[3]*d[0]) + b[3]*(c[0]*d[1]-c[1]*d[0]);
    double m03 = b[0]*(c[1]*d[2]-c[2]*d[1]) - b[1]*(c[0]*d[2]-c[2]*d[0]) + b[2]*(c[0]*d[1]-c[1]*d[0]);
    return a[0]*m00 - a[1]*m01 + a[2]*m02 - a[3]*m03;
}

double evalInteg(const Integrand& integ, const vector<Vec4>& tw) {
    double n = 1.0, d = 1.0;
    for (auto& b : integ.num) n *= det4(tw[b[0]], tw[b[1]], tw[b[2]], tw[b[3]]);
    for (auto& b : integ.den) d *= det4(tw[b[0]], tw[b[1]], tw[b[2]], tw[b[3]]);
    return n / d;
}

Bracket applyPerm(const vector<int>& perm, const Bracket& b) {
    Bracket r = {perm[b[0]], perm[b[1]], perm[b[2]], perm[b[3]]};
    sort(r.begin(), r.end());
    return r;
}

Integrand applyPerm(const vector<int>& perm, const Integrand& integ) {
    Integrand r;
    for (auto& b : integ.num) r.num.push_back(applyPerm(perm, b));
    for (auto& b : integ.den) r.den.push_back(applyPerm(perm, b));
    sort(r.num.begin(), r.num.end());
    sort(r.den.begin(), r.den.end());
    return r;
}

Integrand shiftLoops(const Integrand& integ, int nE, int shift) {
    Integrand r;
    auto s = [&](int idx) -> int {
        if (idx < nE) return idx;
        int l = (idx - nE) / 2, isB = (idx - nE) % 2;
        return nE + 2*(l + shift) + isB;
    };
    for (auto& br : integ.num) {
        Bracket b = {s(br[0]), s(br[1]), s(br[2]), s(br[3])};
        sort(b.begin(), b.end());
        r.num.push_back(b);
    }
    for (auto& br : integ.den) {
        Bracket b = {s(br[0]), s(br[1]), s(br[2]), s(br[3])};
        sort(b.begin(), b.end());
        r.den.push_back(b);
    }
    sort(r.num.begin(), r.num.end());
    sort(r.den.begin(), r.den.end());
    return r;
}

// ================================================================
//  Build symmetry group (dihedral × loop perms)
// ================================================================

vector<GroupElem> buildGroup(int nE, int nL) {
    int nTw = nE + 2*nL;
    vector<GroupElem> result;
    
    vector<vector<int>> dihPerms;
    for (int k = 0; k < nE; k++) {
        vector<int> p(nTw);
        for (int i = 0; i < nE; i++) p[i] = (i+k) % nE;
        for (int i = nE; i < nTw; i++) p[i] = i;
        dihPerms.push_back(p);
    }
    for (int k = 0; k < nE; k++) {
        vector<int> p(nTw);
        for (int i = 0; i < nE; i++) p[i] = (((1-i) % nE) + nE) % nE;
        // Rotate by k
        vector<int> q(nTw);
        for (int i = 0; i < nE; i++) q[i] = (p[i]+k) % nE;
        for (int i = nE; i < nTw; i++) q[i] = i;
        dihPerms.push_back(q);
    }
    sort(dihPerms.begin(), dihPerms.end());
    dihPerms.erase(unique(dihPerms.begin(), dihPerms.end()), dihPerms.end());
    
    vector<int> lo(nL); iota(lo.begin(), lo.end(), 0);
    vector<vector<int>> lPerms;
    do { lPerms.push_back(lo); } while (next_permutation(lo.begin(), lo.end()));
    
    for (auto& dp : dihPerms)
        for (auto& lp : lPerms) {
            GroupElem g; g.perm = dp;
            for (int l = 0; l < nL; l++) {
                g.perm[nE+2*l] = nE+2*lp[l];
                g.perm[nE+2*l+1] = nE+2*lp[l]+1;
            }
            result.push_back(g);
        }
    sort(result.begin(), result.end(), [](auto& a, auto& b){ return a.perm < b.perm; });
    result.erase(unique(result.begin(), result.end(), 
        [](auto& a, auto& b){ return a.perm == b.perm; }), result.end());
    return result;
}

// ================================================================
//  Parse ansatz output
// ================================================================

Integrand parseIntegrand(const string& line, int nE) {
    Integrand integ;
    // Parse: C[i] Det[{...}] Det[{...}] / (Det[{...}] Det[{...}])
    
    auto parseIdx = [&](const string& s) -> int {
        if (s[0] == 'Z') return stoi(s.substr(2, s.size()-3)) - 1;
        if (s[0] == 'A') { int l = stoi(s.substr(2, s.size()-3)); return nE + 2*(l-1); }
        if (s[0] == 'B') { int l = stoi(s.substr(2, s.size()-3)); return nE + 2*(l-1) + 1; }
        return -1;
    };
    
    // Find all Det[{...}] occurrences
    vector<Bracket> allBrackets;
    size_t pos = 0;
    while ((pos = line.find("Det[{", pos)) != string::npos) {
        size_t end = line.find("}]", pos);
        string inner = line.substr(pos+5, end-pos-5);
        // Parse comma-separated list
        vector<int> indices;
        stringstream ss(inner);
        string token;
        while (getline(ss, token, ',')) indices.push_back(parseIdx(token));
        Bracket br = {indices[0], indices[1], indices[2], indices[3]};
        sort(br.begin(), br.end());
        allBrackets.push_back(br);
        pos = end + 2;
    }
    
    // Split into num/den by finding "/ ("
    size_t slashPos = line.find("/ (");
    if (slashPos == string::npos) {
        // All numerator
        integ.num = allBrackets;
    } else {
        // Count brackets before and after slash
        int numBefore = 0;
        size_t p = 0;
        while ((p = line.find("Det[{", p)) != string::npos && p < slashPos) {
            numBefore++; p += 5;
        }
        for (int i = 0; i < numBefore; i++) integ.num.push_back(allBrackets[i]);
        for (int i = numBefore; i < (int)allBrackets.size(); i++) integ.den.push_back(allBrackets[i]);
    }
    
    sort(integ.num.begin(), integ.num.end());
    sort(integ.den.begin(), integ.den.end());
    return integ;
}

// ================================================================
//  Previous loop result storage
// ================================================================

struct LoopResult {
    vector<double> coeffs;
    vector<vector<Integrand>> orbitImages; // shifted loop labels
};

double evalRes(const LoopResult& res, const vector<Vec4>& tw) {
    double val = 0;
    for (int i = 0; i < (int)res.coeffs.size(); i++) {
        if (abs(res.coeffs[i]) < 1e-15) continue;
        for (auto& img : res.orbitImages[i])
            val += res.coeffs[i] * evalInteg(img, tw);
    }
    return val;
}

// ================================================================
//  Collinear limit: direct evaluation
// ================================================================

// At A[1]=Z[2], B[1]=αZ[1]+γZ[3]:
// - ⟨Z1 Z2 A1 B1⟩ = 0 and ⟨Z2 Z3 A1 B1⟩ = 0
// - Only orbit images with BOTH in denominator contribute (double pole)
// - Cancel these two factors, evaluate the rest directly

double evalCollinear(const Integrand& img, const vector<Vec4>& tw,
                     int nE, double alpha, double gamma) {
    // The two zero brackets (sorted)
    Bracket br12, br23;
    {
        array<int,4> a = {0, 1, nE, nE+1}; sort(a.begin(), a.end()); br12 = a;
        array<int,4> b = {1, 2, nE, nE+1}; sort(b.begin(), b.end()); br23 = b;
    }
    
    // Check both are in denominator
    if (count(img.den.begin(), img.den.end(), br12) < 1 ||
        count(img.den.begin(), img.den.end(), br23) < 1)
        return 0.0;
    
    // Build collinear twistors
    vector<Vec4> ctw = tw;
    ctw[nE] = ctw[1]; // A[1] = Z[2]
    for (int k = 0; k < 4; k++)
        ctw[nE+1][k] = alpha*ctw[0][k] + gamma*ctw[2][k]; // B[1] = αZ[1]+γZ[3]
    
    // Evaluate numerator
    double num = 1.0;
    for (auto& b : img.num) {
        num *= det4(ctw[b[0]], ctw[b[1]], ctw[b[2]], ctw[b[3]]);
        if (num == 0.0) return 0.0;
    }
    
    // Evaluate denominator, skipping one copy each of br12 and br23
    double den = 1.0;
    bool skip12 = false, skip23 = false;
    for (auto& b : img.den) {
        if (b == br12 && !skip12) { skip12 = true; continue; }
        if (b == br23 && !skip23) { skip23 = true; continue; }
        double v = det4(ctw[b[0]], ctw[b[1]], ctw[b[2]], ctw[b[3]]);
        if (abs(v) < 1e-30) return 0.0;
        den *= v;
    }
    
    return num / den;
}

// ================================================================
//  Solve linear system
// ================================================================

vector<double> solveLS(vector<vector<double>>& M, vector<double>& rhs) {
    int nEqs = M.size(), nVars = M[0].size();
    vector<vector<double>> aug(nEqs, vector<double>(nVars+1));
    for (int i = 0; i < nEqs; i++) {
        for (int j = 0; j < nVars; j++) aug[i][j] = M[i][j];
        aug[i][nVars] = rhs[i];
    }
    
    int rank = 0;
    vector<int> pivCol(nVars, -1);
    for (int col = 0; col < nVars && rank < nEqs; col++) {
        int piv = -1; double best = 1e-10;
        for (int r = rank; r < nEqs; r++)
            if (abs(aug[r][col]) > best) { best = abs(aug[r][col]); piv = r; }
        if (piv < 0) continue;
        swap(aug[rank], aug[piv]);
        double inv = 1.0/aug[rank][col];
        for (int j = col; j <= nVars; j++) aug[rank][j] *= inv;
        for (int r = 0; r < nEqs; r++) {
            if (r == rank || abs(aug[r][col]) < 1e-14) continue;
            double f = aug[r][col];
            for (int j = col; j <= nVars; j++) aug[r][j] -= f*aug[rank][j];
        }
        pivCol[col] = rank; rank++;
    }
    
    vector<double> x(nVars, 0);
    for (int c = 0; c < nVars; c++)
        if (pivCol[c] >= 0) x[c] = aug[pivCol[c]][nVars];
    
    // Check
    double maxRes = 0;
    for (int i = 0; i < nEqs; i++) {
        double r = -rhs[i];
        for (int j = 0; j < nVars; j++) r += M[i][j]*x[j];
        maxRes = max(maxRes, abs(r));
    }
    cerr << "    Rank: " << rank << "/" << nVars << ", residual: " << maxRes << "\n";
    
    // Count free (unfixed) variables
    int nFree = 0;
    for (int c = 0; c < nVars; c++) if (pivCol[c] < 0) nFree++;
    if (nFree > 0) cerr << "    WARNING: " << nFree << " unfixed coefficients\n";
    
    return x;
}

// ================================================================
//  Main bootstrap
// ================================================================

int main(int argc, char* argv[]) {
    if (argc < 3) { cerr << "Usage: scboot <nPoints> <maxLoops>\n"; return 1; }
    int nPts = atoi(argv[1]);
    int maxL = atoi(argv[2]);
    
    cerr << "═══════════════════════════════════════\n";
    cerr << "  SCBootstrap[" << nPts << ", " << maxL << "]\n";
    cerr << "═══════════════════════════════════════\n\n";
    
    mt19937 rng(777);
    uniform_real_distribution<double> dist(-2.0, 2.0);
    auto rv = [&]() -> Vec4 { return {dist(rng), dist(rng), dist(rng), dist(rng)}; };
    
    vector<LoopResult> prevResults; // prevResults[l] = Res[l+1]
    
    for (int L = 1; L <= maxL; L++) {
        cerr << "──────────── Loop level " << L << " ────────────\n";
        auto tL = chrono::steady_clock::now();
        
        int nE = nPts;
        int nTw = nE + 2*L;
        
        // ---- Step 1: Run ansatz generator ----
        cerr << "  Generating ansatz...\n";
        string cmd = "./ansatz " + to_string(nPts) + " " + to_string(L) + " 2>/dev/null";
        FILE* pipe = popen(cmd.c_str(), "r");
        if (!pipe) { cerr << "  Failed to run ./ansatz\n"; return 1; }
        
        string output;
        char buf[8192];
        while (fgets(buf, sizeof(buf), pipe)) output += buf;
        pclose(pipe);
        
        // Parse orbit reps
        vector<Integrand> orbitReps;
        istringstream iss(output);
        string line;
        while (getline(iss, line)) {
            if (line.find("C[") != string::npos && line.find("Det") != string::npos) {
                orbitReps.push_back(parseIntegrand(line, nE));
            }
        }
        cerr << "  Orbit reps: " << orbitReps.size() << "\n";
        
        // ---- Step 2: Build group and orbit images ----
        cerr << "  Building group and orbit images...\n";
        auto group = buildGroup(nE, L);
        cerr << "  Group size: " << group.size() << "\n";
        
        // For each orbit rep, generate all distinct group images
        vector<vector<Integrand>> orbitImages(orbitReps.size());
        for (int i = 0; i < (int)orbitReps.size(); i++) {
            set<Integrand> seen;
            for (auto& g : group) {
                Integrand img = applyPerm(g.perm, orbitReps[i]);
                if (seen.insert(img).second)
                    orbitImages[i].push_back(img);
            }
        }
        int totalExpanded = 0;
        for (auto& oi : orbitImages) totalExpanded += oi.size();
        cerr << "  Total expanded: " << totalExpanded << "\n";
        
        // ---- Step 3: Build collinear matrix ----
        // One equation per kinematic point: double-pole matching
        cerr << "  Building collinear matrix...\n";
        int nReps = orbitReps.size();
        int nEqs = nReps + 20;
        
        vector<vector<double>> M(nEqs, vector<double>(nReps));
        vector<double> rhs(nEqs, 0.0);
        
        for (int k = 0; k < nEqs; k++) {
            if (k % 10 == 0) cerr << "    Eq " << k << "/" << nEqs << "\r" << flush;
            
            // Random kinematics
            vector<Vec4> tw(nTw);
            for (int i = 0; i < nTw; i++) tw[i] = rv();
            double alpha = 0.5 + dist(rng); // avoid near-zero
            double gamma = 0.5 + dist(rng);
            
            // Matrix entries: sum evalCollinear over orbit images, multiply by αγ
            for (int i = 0; i < nReps; i++) {
                double val = 0;
                for (auto& img : orbitImages[i])
                    val += evalCollinear(img, tw, nE, alpha, gamma);
                M[k][i] = alpha * gamma * val;
            }
            
            // RHS: -Res[L-1] (already multiplied by αγ)
            if (L == 1) {
                rhs[k] = -1.0;
            } else {
                vector<Vec4> ctw = tw;
                ctw[nE] = ctw[1];
                for (int j = 0; j < 4; j++)
                    ctw[nE+1][j] = alpha*ctw[0][j] + gamma*ctw[2][j];
                double resVal = evalRes(prevResults[L-2], ctw);
                rhs[k] = -(1.0/L) * resVal;
            }
        }
        cerr << "\n";
        
        // ---- Step 4: Solve ----
        cerr << "  Solving...\n";
        auto coeffs = solveLS(M, rhs);
        
        // ---- Step 5: Store result ----
        // Shift loop labels by +1 for use at next level
        LoopResult res;
        res.coeffs = coeffs;
        res.orbitImages.resize(nReps);
        for (int i = 0; i < nReps; i++) {
            for (auto& img : orbitImages[i]) {
                res.orbitImages[i].push_back(shiftLoops(img, nE, 1));
            }
        }
        prevResults.push_back(res);
        
        // ---- Output ----
        auto tEnd = chrono::steady_clock::now();
        cerr << "  Time: " << chrono::duration<double>(tEnd-tL).count() << " s\n";
        
        // Print solution
        cerr << "  Solution:\n";
        int nFree = 0;
        for (int i = 0; i < nReps; i++) {
            if (abs(coeffs[i]) > 1e-12) {
                cerr << "    C[" << i+1 << "] = " << coeffs[i] << "\n";
            } else {
                nFree++;
            }
        }
        if (nFree > 0) cerr << "    (" << nFree << " unfixed coefficients set to 0)\n";
        
        // Save to file
        string fname = "bootstrap_L" + to_string(L) + "_n" + to_string(nPts) + ".dat";
        ofstream fout(fname);
        fout << "# SCBootstrap result: " << nPts << "-point, " << L << "-loop\n";
        fout << "# nOrbitReps = " << nReps << "\n";
        for (int i = 0; i < nReps; i++) {
            fout << "C[" << L << "," << i+1 << "] = " << coeffs[i] << "\n";
        }
        fout.close();
        cerr << "  Saved to " << fname << "\n\n";
    }
    
    cerr << "═══════════════════════════════════════\n";
    cerr << "  SCBootstrap complete.\n";
    cerr << "═══════════════════════════════════════\n";
    
    return 0;
}