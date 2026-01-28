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

vector<vector<int>> t;
vector<int> d, max_d;
int n;

void input(){
    cin >> n;
    t.resize(n);
    d.resize(n);
    max_d.assign(n, 0);
    int u, v;
    for(int i = 1; i < n; i++){
        cin >> u >> v;
        u--, v--;
        t[u].push_back(v);
        t[v].push_back(u);
    }
}

void dfs(int node, int par, int dis){
    d[node] = dis;
    for(auto &child: t[node]){
        if(child != par){
            dfs(child, node, dis + 1);
        }
    }
}

void find_max_d(int node, int par, int dis){
    max_d[node] = max(max_d[node], dis);
    for(auto &child: t[node]){
        if(child != par){
            find_max_d(child, node, dis + 1);
        }
    }
}

void solve()
{
    input();
    dfs(0, -1, 0);
    int d1_node = max_element(all(d)) - d.begin();
    dfs(d1_node, -1, 0);
    int d2_node = max_element(all(d)) - d.begin(), diameter = *max_element(all(d));
    find_max_d(d1_node, -1, 0);
    find_max_d(d2_node, -1, 0);
    sort(all(max_d));
    for(int i = 1; i <= n; i++){
        int seperated = lower_bound(all(max_d), i) - max_d.begin();
        cout << min(seperated + 1, n) << (i == n ? '\n' : ' ');
    }
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