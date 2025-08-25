#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
vector<vector<int>>g;
vector<int>reachable;
vector<bool>visited;
set<pair<int,int>>cut_edges;
int dfs_cnt;
vector<int>dfs_num,dfs_low;

void dfs_reach(int node, int parent){
    visited[node] = true;
    for(auto &adj: g[node]){
        if(!visited[adj])
            dfs_reach(adj,node);
        if(adj!=parent)
            reachable[node]|=reachable[adj];
    }
}

void find_cut_edges(int node, int par){
    visited[node] = true;
    dfs_num[node] = dfs_cnt++;
    dfs_low[node] = dfs_num[node];
    for(auto &adj: g[node]){
        if(!visited[adj]){
            find_cut_edges(adj,node);
            if(dfs_low[adj]>dfs_num[node] and reachable[node] and reachable[adj]){
                cut_edges.insert({node,adj});
            }
            dfs_low[node] = min(dfs_low[node],dfs_low[adj]);
        }else if(adj!=par){
            dfs_low[node] = min(dfs_low[node],dfs_num[adj]);
        }
    }
}

void clear_assign(int n){
    dfs_cnt = 0;
    dfs_num.clear();
    dfs_low.clear();
    cut_edges.clear();
    visited.clear();
    g.clear();
    reachable.clear();
    g.resize(n);
    reachable.resize(n);
    dfs_num.resize(n);
    dfs_low.resize(n);
    visited.assign(n,false);
}

void solve()
{
    int n,m;
    cin>>n>>m;
    clear_assign(n);
    vector<pair<int,int>>edges(m);
    for(auto &[u,v]: edges){
        cin>>u>>v;
        u--,v--;
        g[u].push_back(v);
        g[v].push_back(u);
    }
    reachable[n-1] = true;
    dfs_reach(0,-1);
    visited.assign(n,false);
    find_cut_edges(0,-1);
    visited.assign(n,false);
    queue<pair<int,int>>q;
    vector<int>ans(n,-2);
    for(int i = 0; i<m; i++){
        auto &[u,v] = edges[i];
        if(cut_edges.count(make_pair(u,v)) or cut_edges.count(make_pair(v,u))){
            if(!visited[u]){
                q.push({u,i});
                ans[u] = i;
                visited[u] = true;
            }
            if(!visited[v]){
                q.push({v,i});
                ans[v] = i;
                visited[v] = true;
            }
        }
    }
    while(!q.empty()){
        auto [node,id] = q.front();
        q.pop();
        for(auto &adj: g[node]){
            if(!visited[adj]){
                visited[adj] = true;
                ans[adj] = id;
                q.push({adj,id});
            }
        }
    }
    int k;
    cin>>k;
    while(k--){
        int node;
        cin>>node;
        cout<<ans[node-1]+1<<" ";
    }
    cout<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}