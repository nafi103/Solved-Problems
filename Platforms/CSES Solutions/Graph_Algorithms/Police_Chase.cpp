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

vector<bool>visited;
vector<vector<int>> g, capacity;
int n, m;

void input(){
    int u, v;
    cin >> n >> m;
    g.resize(n);
    visited.assign(n, false);
    capacity.assign(n,vector<int>(n, 0));
    for(int i = 0; i < m; i++){
        cin >> u >> v;
        u--, v--;
        g[u].push_back(v);
        g[v].push_back(u);
        capacity[u][v] ++;
        capacity[v][u] ++;
    }
}

int bfs(int s, int t, vector<int> &parent){
    parent.assign(n, -1);
    queue<pair<int,int>> q;
    q.push({s, inf});
    parent[s] = -2;
    while(!q.empty()){
        auto [node, c] = q.front();
        q.pop();
        for(auto &adj: g[node]){
            if(parent[adj] == -1 and capacity[node][adj]){
                parent[adj] = node;
                int newflow = min(c, capacity[node][adj]);
                if(adj == t)
                    return newflow;
                q.push({adj, newflow});
            }
        }
    }
    return 0;
}

void dfs(int node){
    visited[node] = true;
    for(auto &adj: g[node]){
        if(!visited[adj] and capacity[node][adj])
            dfs(adj);
    }
}

void solve()
{
    input();
    int flow = 0, newflow;
    vector<int> parent;
    while(newflow = bfs(0, n - 1, parent)){
        flow += newflow;
        int cur = n - 1;
        while(cur != 0){
            int par = parent[cur];
            capacity[par][cur] -= newflow;
            capacity[cur][par] += newflow;
            cur = par;
        }
    }
    cout << flow << endl;
    dfs(0);
    for(int node = 0; node < n; node++){
        if(!visited[node])
            continue;
        for(auto &adj: g[node]){
            if(!visited[adj])
                cout << node + 1 << " " << adj + 1 << endl;
        }
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