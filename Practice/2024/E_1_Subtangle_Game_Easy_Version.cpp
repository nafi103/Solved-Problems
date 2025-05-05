#pragma GCC optimize("Ofast")
#include<bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
#define int long long
using namespace std;
using namespace __gnu_pbds;
#define endl "\n"
#define all(x) x.begin(), x.end()
#define rall(x) x.rbegin(), x.rend()
#define YN(con) printf((con ? "T" : "N")); 
#define yn(con) printf((con ? "Yes\n" : "No\n"));
#define unq(x) sort(all(x)), x.resize(unique(all(x)) - x.begin())
typedef tree<int, null_type, less_equal<int>, rb_tree_tag, tree_order_statistics_node_update> PBDS;
template <typename T> istream& operator>>(istream& in, vector<T>& a) {for(auto &x : a) in >> x; return in;};
template <typename T> ostream& operator<<(ostream& out, vector<T>& a) {for(auto &x : a) out << x << ' '; return out;};
template <class A, class B> ostream &operator<<(ostream &out, const pair<A, B> &a) { return out << "(" << a.first << ", " << a.second << ")"; }
template <class A, class B> istream &operator>>(istream &in, pair<A, B> &a) { return in >> a.first >> a.second; }
inline int read(){ int s = 0, w = 1; char ch = getchar(); while (ch < '0' || ch > '9') { if (ch == '-') w = -1; ch = getchar();} while (ch >= '0' && ch <= '9') s = s * 10 + ch - '0', ch = getchar(); return s * w;}
inline void write(int x) { if (x < 0) { x = -x; putchar('-'); } if (x > 9) write(x / 10); putchar(x % 10 + 48); return;}
#ifndef ONLINE_JUDGE
#define dbg(...) cerr << "[" << #__VA_ARGS__ << "]:", debug_out(__VA_ARGS__)
#else
#define dbg(x)
#endif
const int mod = 1e9 + 7;
const int M = 301;
bool dp[M][M][M];

bool play(const vector<vector<int>>& grid, int n, int m, int val, int strt, int stc) {
    for (int i = strt; i < n; ++i) {
        for (int j = stc; j < m; ++j) {
            if (grid[i][j] == val) {
                return true;
            }
        }
    }
    return false;
}

bool solve(vector<int>& a, const vector<vector<int>>& grid, int n, int m) {
    int l = a.size();
    for (int i = 0; i <= l; ++i) {
        for (int r = 0; r <= n; ++r) {
            for (int c = 0; c <= m; ++c) {
                dp[i][r][c] = false;
            }
        }
    }

    for (int r = 0; r <= n; ++r) {
        for (int c = 0; c <= m; ++c) {
            dp[l][r][c] = false;
        }
    }

    for (int i = l - 1; i >= 0; --i) {
        for (int r = n - 1; r >= 0; --r) {
            for (int c = m - 1; c >= 0; --c) {
                dp[i][r][c] = false;
                if (play(grid, n, m, a[i], r, c)) {
                    int nr, nc;
                    for (int i1 = r; i1 < n; ++i1) {
                        for (int j1 = c; j1 < m; ++j1) {
                            if (grid[i1][j1] == a[i]) {
                                nr = i1 + 1;
                                nc = j1 + 1;
                                if (nr <= n && nc <= m && !dp[i + 1][nr][nc]) {
                                    dp[i][r][c] = true;
                                    break;
                                }
                            }
                        }
                        if (dp[i][r][c]) break;
                    }
                }
            }
        }
    }

    return dp[0][0][0];
}

inline void solve() {
    int l = read(), n = read(), m = read();

    vector<int> a(l);
    cin >> a;

    vector<vector<int>> grid(n, vector<int>(m));
    for (int i = 0; i < n; ++i) {
        cin >> grid[i];
    }
    bool ans = solve(a, grid, n, m);
    YN(ans);
}
int32_t main() {
    int tc = read();
    for (int i = 1; i <= tc; i++) {
        // cout << "Case " << i << ": ";
        // cerr << "Case " << i << ": ";
        solve();
        printf("\n");
    }
    return 0;
}