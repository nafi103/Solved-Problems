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
set<int> f[N];
vector<int> g[N];
int n, cf[N], cg[N];
bool visited[N];

void input(){
    int m1, m2;
    cin >> n >> m1 >> m2;

    for(int i = 0; i < n; i++){
        g[i].clear();
        f[i].clear();
    }

    for(int i = 0, u, v; i < m1; i++){
        cin >> u >> v;
        u--, v--;
        f[u].insert(v);
        f[v].insert(u);
    }

    for(int i = 0, u, v; i < m2; i++){
        cin >> u >> v;
        u--, v--;
        g[u].push_back(v);
        g[v].push_back(u);
    }
}

void dfs_g(int node, int &id){
    cg[node] = id;
    visited[node] = true;
    for(auto &adj: g[node]){
        if(!visited[adj])
            dfs_g(adj, id);
    }
}

void dfs_f(int node, int &id){
    cf[node] = id;
    visited[node] = true;
    for(auto &adj: f[node]){
        if(!visited[adj])
            dfs_f(adj, id);
    }
}

void solve()
{
    input();

    int ans = 0;
    vector<int> roots;

    fill(visited, visited + n, false);
    int c_num = 0;
    for(int node = 0; node < n; node++){
        if(!visited[node]){
            roots.push_back(node);
            dfs_g(node, c_num);
            c_num++;
        }
    }

    for(int node = 0; node < n; node++){
        vector<int> ers;
        for(auto &adj: f[node]){
            if(cg[node] != cg[adj]){
                ers.push_back(adj);
            }
        }
        for(auto &x: ers){
            ans++;
            f[node].erase(x);
            f[x].erase(node);
        }
    }

    c_num = 0;
    fill(visited, visited + n, false);
    for(int node = 0; node < n; node++){
        if(!visited[node]){
            if(c_num == cg[node]){
                dfs_f(node, c_num);
                c_num++;
            }else{
                ans++;
                dfs_f(node, cg[node]);
            }
        }
    }

    cout << ans << endl;
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