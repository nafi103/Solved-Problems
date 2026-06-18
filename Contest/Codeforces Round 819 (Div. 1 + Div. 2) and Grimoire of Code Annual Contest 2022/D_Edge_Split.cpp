#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define sz(x) (int)(x).size()
#define all(x) x.begin(), x.end()
#define endl "\n"
const int mod = 998244353;
const int inf = 1e18 + 10;
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << "Line " << __LINE__ << ": " << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
const int N = 2e5 + 10;
int depth[N], parent_edge[N];
bool ans[N], visited[N];
vector<pair<int, int>> back_edges;
set<int> triangle;
vector<vector<pair<int, int>>> g(N);
 void dfs(int node, int par, int d) {
    visited[node] = true;
    depth[node] = d;
    for (auto &[child, id] : g[node]) {
        if (!visited[child]) {
            ans[id] = 1;
            parent_edge[child] = id;
            dfs(child, node, d + 1);
        } else if (child != par && depth[child] < depth[node]) {
            back_edges.push_back({id, node});
            triangle.insert(node);
            triangle.insert(child);
        }
    }
}
 void solve() {
    int n, m;
    cin >> n >> m;
    triangle.clear();
    back_edges.clear();
    for (int i = 0; i < n; i++) {
        g[i].clear();
        visited[i] = false;
        parent_edge[i] = -1;
    }
    for (int i = 0; i < m; i++) ans[i] = 0;
    for (int i = 0; i < m; i++) {
        int u, v; cin >> u >> v;
        u--, v--;
        g[u].push_back({v, i});
        g[v].push_back({u, i});
    }
    dfs(0, -1, 0);
    if (back_edges.size() == 3 && triangle.size() == 3) {
        int w = -1, max_d = -1;
        for (int node : triangle) {
            if (depth[node] > max_d) {
                max_d = depth[node];
                w = node;
            }
        }
        int back_id = -1;
        for (auto &edge : back_edges) {
            if (edge.second == w) {
                back_id = edge.first;
                break;
            }
        }
        ans[back_id] = 1;
        ans[parent_edge[w]] = 0;
    }
     for (int i = 0; i < m; i++) 
        cout << ans[i];
    cout << endl;
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}