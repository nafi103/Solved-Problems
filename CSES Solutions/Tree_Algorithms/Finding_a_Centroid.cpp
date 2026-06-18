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
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
vector<int> subtree_size;
vector<vector<int>> t;
int root = -1,n;

void dfs(int node, int par)
{
    subtree_size[node] = 1;
    for(auto &child: t[node]){
        if(child!=par){
            dfs(child, node);
            subtree_size[node] += subtree_size[child];
        }
    }
}

int find_root(int node){
    int heavy_child = -1;
    for(auto &child: t[node]){
        if(subtree_size[child]>n/2){
            heavy_child = child;
            break;
        }
    }
    if(heavy_child==-1){
        return node;
    }
    subtree_size[node] -= subtree_size[heavy_child];
    subtree_size[heavy_child] += subtree_size[node];
    return find_root(heavy_child);
}

void solve()
{
    cin >> n;
    t.resize(n + 1);
    subtree_size.assign(n + 1, -1);
    for (int i = 1; i < n; i++)
    {
        int u, v;
        cin >> u >> v;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    dfs(1, 0);
    cout<<find_root(1)<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}