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

/* 
Idea is that only the bridges can be assigned with any value, all the rest is fixed. But I need to find
if the answer exist too. This is the harder part.

1 - 2
|   | --> Odd cycle is problematic. In cycle all value must be the same
3 - -

But here, 1 -> 2 -> 3 has different value than 1 -> 3. Only valid option here is if all of the nodes are 0
If any one of has positive value then that's an invalid case.

Psuedo:

1. Input
2. Find all the bridges. Remove the bridges.
3. Find the components.
5. return (single components and -1) ^ V;
*/

vector<pair<int,int>> bridges;
const int N = 2e5 + 10, unvisited = -1;
int n, value[N], m, V, dfs_num[N], dfs_low[N], dfs_cnt;
vector<set<int>> g(N);
vector<bool> visited(N);
vector<int> cycle, parity(N);
bool odd_cycle;

void input(){
    bridges.clear();
    cin >> n >> m >> V;
    for(int i = 0; i < n; i++){
        cin >> value[i];
        dfs_num[i] = unvisited;
        visited[i] = false;
        g[i].clear();
    }

    for(int i = 0, u, v; i < m; i++){
        cin >> u >> v;
        u--, v--;
        g[u].insert(v);
        g[v].insert(u);
    }
}

void find_bridges(int node, int par){
    dfs_num[node] = dfs_low[node] = dfs_cnt++;
    for(auto &adj: g[node]){
        if(dfs_num[adj] == unvisited){
            find_bridges(adj, node);
            if (dfs_low[adj] > dfs_num[node])
                bridges.push_back({node, adj});
            dfs_low[node] = min(dfs_low[node], dfs_low[adj]);
        }else if(adj != par){
            dfs_low[node] = min(dfs_low[node], dfs_num[adj]);
        }
    }
}

void dfs(int node, int par, int p){
    cycle.push_back(node);
    visited[node] = true;
    parity[node] = p;

    for(auto &adj: g[node]){
        if(!visited[adj]){
            dfs(adj, node, p ^ 1);
        }else if(adj != par and (parity[node] == parity[adj])){
            odd_cycle = true;
        }
    }
}

void solve()
{
    input();
    dfs_cnt = 0;
    find_bridges(0, -1);
    // for(int i = 0; i < n; i++){
    //     cerr << dfs_num[i] << " ";
    // }
    // cerr << endl;
    for(auto &[u, v]: bridges){
        g[u].erase(v);
        g[v].erase(u);
    }

    int ans = 1;
    for(int i = 0; i < n; i++){
        if(!visited[i]){
            cycle.clear();
            odd_cycle = false;
            dfs(i, -1, 0);

            set<int> available_values;
            bool positive = false, all_neg = true;
            for(auto &node: cycle){
                if(value[node] >= 0){
                    available_values.insert(value[node]);
                    if(value[node])
                        positive = true;
                    all_neg = false;
                }
            }

            if(sz(available_values) > 1){
                cout << 0 << endl;
                return;
            }

            if(!all_neg){
                if(odd_cycle and positive){
                    cout << 0 << endl;
                    return;
                }
            }

            if(all_neg and !odd_cycle){
                ans = (ans * V) % mod;
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