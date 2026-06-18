#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                            \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
vector<vector<int>> t, nodes;
vector<set<int>> new_tree;
vector<int> _size, connected, in_tree, mx, smx, final_ans, color, black;
vector<int> dp; // Stores value of subtree rooted at u (for dfs1)
vector<bool> visited, special;
 void assign(int n)
{
    black.clear();
    color.clear();
    final_ans.clear();
    special.clear();
    t.clear();
    new_tree.clear();
    nodes.clear();
    _size.clear();
    connected.clear();
    in_tree.clear();
    mx.clear();
    smx.clear();
    visited.clear();
    dp.clear(); // Clear DP array
     t.resize(n);
    in_tree.resize(n);
    visited.assign(n, false);
    special.assign(n, false);
}
 // Standard component finding DFS
void dfs(int node)
{
    visited[node] = true;
    connected.push_back(node);
    for (auto &child : t[node])
    {
        if (!visited[child] and !special[child])
        {
            dfs(child);
        }
    }
}
 // PASS 1: Bottom-up DP
// Calculates the max value u can contribute to its parent p
void dfs1(int u, int p) {
    int best = 0;
    int second_best = 0;
     for (auto &v : new_tree[u]) {
        if (v == p) continue;
        dfs1(v, u);
        int val = dp[v];
        if (val >= best) {
            second_best = best;
            best = val;
        } else if (val > second_best) {
            second_best = val;
        }
    }
     mx[u] = best;
    smx[u] = second_best;
     // Calculate DP value (u acting as a child in a tree rooted above)
    if (color[u]) { // Special Node
        dp[u] = 1 + best;
    } else { // White Component
        // Formula: max_child + size + black - (deg > 1) - (is_root ? 0 : 1)
        // Since this is dfs1, u is NEVER the root of the full tree, so we subtract 1
        int deg = new_tree[u].size();
        int val = best + _size[u] + black[u];
        if (deg > 1) val -= 1;
        val -= 1; 
        dp[u] = val;
    }
}
 // PASS 2: Top-down Rerooting
// p_val is the value coming from the "parent" (treating the parent as a child)
void dfs2(int u, int p, int p_val) {
    // 1. Calculate the Final Answer for u as the absolute ROOT
    // The best path is either from one of the original children (mx[u]) 
    // or from the parent direction (p_val)
    int best_neighbor = max(mx[u], p_val);
     if (color[u]) {
        final_ans[u] = 1 + best_neighbor;
    } else {
        int deg = new_tree[u].size();
        int val = best_neighbor + _size[u] + black[u];
        if (deg > 1) val -= 1;
        // If u is root, we subtract 1 only if degree == 1. 
        // Otherwise (degree != 1), we subtract 0.
        if (deg == 1) val -= 1; 
        final_ans[u] = val;
    }
     // 2. Propagate values to children
    for (auto &v : new_tree[u]) {
        if (v == p) continue;
         // Determine max value entering u excluding v
        // If v was the one providing mx[u], use smx[u]. Otherwise use mx[u].
        int use_val = (dp[v] == mx[u]) ? smx[u] : mx[u];
        // Also compare with what came from u's parent
        use_val = max(use_val, p_val);
         // Calculate what u passes down to v
        // u acts as a child of v in the rerooted perspective
        int pass_val;
        if (color[u]) {
            pass_val = 1 + use_val;
        } else {
            int deg = new_tree[u].size();
            int val = use_val + _size[u] + black[u];
            if (deg > 1) val -= 1;
            val -= 1; // u is not root (it is child of v)
            pass_val = val;
        }
         dfs2(v, u, pass_val);
    }
}
 void solve()
{
    int n, m;
    cin >> n >> m;
    assign(n);
     for (int i = 0; i < m; i++)
    {
        int x;
        cin >> x;
        x--;
        special[x] = true;
    }
     for (int i = 1; i < n; i++)
    {
        int u, v;
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
     // Build compressed graph
    for (int node = 0; node < n; node++)
    {
        if (visited[node])
            continue;
        if (special[node])
        {
            visited[node] = true;
            in_tree[node] = nodes.size();
            _size.push_back(1);
            color.push_back(1); // 1 = Special
            nodes.push_back({node});
            continue;
        }
        connected.clear();
        dfs(node);
        _size.push_back(connected.size());
        color.push_back(0); // 0 = White component
        for (auto &x : connected)
        {
            in_tree[x] = nodes.size();
        }
        nodes.push_back(connected);
    }
     black.assign(nodes.size(), 0);
    new_tree.resize(nodes.size());
        for (int i = 0; i < n; i++)
    {
        int my_node = in_tree[i];
        for (auto &child : t[i])
        {
            int other = in_tree[child];
            if (my_node != other)
            {
                if(color[my_node])
                    black[other]++;
                else
                    black[my_node]++;
                new_tree[my_node].insert(other);
                new_tree[other].insert(my_node);
            }
        }
    }
     for(auto &x: black) x >>= 1;
     // Initialize Rerooting Arrays
    int sz_nodes = nodes.size();
    mx.assign(sz_nodes, 0);
    smx.assign(sz_nodes, 0);
    dp.assign(sz_nodes, 0);
    final_ans.assign(sz_nodes, 0);
     if(sz_nodes > 0) {
        // Pass 1: Calculate subtree values (rooted at 0)
        dfs1(0, -1);
        // Pass 2: Rotate root and push values down
        dfs2(0, -1, 0);
    }
     vector<int> ans(n);
    for (int i = 0; i < nodes.size(); i++)
    {
        for (auto &node : nodes[i])
        {
            ans[node] = final_ans[i];
        }
    }
     for (int z = 0; z < ans.size(); z++)
        cout << ans[z] << " \n"[z + 1 == ans.size()];
}
 int32_t main()
{
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for (int z = 1; z <= t; z++)
    {
        solve();
    }
}