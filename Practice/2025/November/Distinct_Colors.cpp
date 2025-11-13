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

vector<vector<int>> t;
vector<int> color, distinct_color;
vector<set<int>> tmp;

void dfs(int node, int par){
    tmp[node] = {color[node]};
    int heavy_child = node, _size = 0;
    for(auto &child: t[node]){
        if(child!=par){
            dfs(child, node);
            if(sz(tmp[child])>_size){
                _size = sz(tmp[child]);
                heavy_child = child;
            }
        }
    }
    swap(tmp[node], tmp[heavy_child]);
    for(auto &child: t[node]){
        if(child!=par){
            for(auto &col: tmp[child])
                tmp[node].insert(col);
            tmp[child].clear();
        }
    }
    distinct_color[node] = sz(tmp[node]);
}

void solve()
{
    int n;
    cin >> n;
    t.resize(n);
    tmp.resize(n);
    color.resize(n);
    distinct_color.resize(n);
    for(auto &x: color){
        cin >> x;
    }
    for (int i = 1; i < n; i++){
        int u, v;
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
    dfs(0, -1);
    for(auto &x: distinct_color){
        cout << x << " ";
    }
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
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}