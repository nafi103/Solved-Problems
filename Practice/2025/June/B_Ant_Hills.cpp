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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
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
vector<int> dfs_num, dfs_low;
vector<bool>visited,articulation_point;
int curr_dfs, root_child;

void dfs(int node, int parent){
    visited[node] = true;
    dfs_num[node] = ++curr_dfs;
    dfs_low[node] = dfs_num[node];
    for(auto &nbr: g[node]){
        if(!visited[nbr]){
            dfs(nbr,node);
            if(node==1)
                root_child++;
            if(dfs_num[node]<=dfs_low[nbr])
                articulation_point[node] = true;
            dfs_low[node] = min(dfs_low[node],dfs_low[nbr]);
        }else if(nbr!=parent){
            dfs_low[node] = min(dfs_low[node],dfs_num[nbr]);
        }
    }
}

void solve()
{
    curr_dfs = 0;
    root_child = 0;
    g.clear();
    articulation_point.clear();
    dfs_low.clear();
    dfs_num.clear();
    visited.clear();
    int n,m;
    cin>>n>>m;
    articulation_point.assign(n+1,false);
    g.resize(n+1);
    dfs_low.resize(n+1);
    dfs_num.resize(n+1);
    visited.assign(n+1,false);
    while(m--){
        int u,v;
        cin>>u>>v;
        g[u].push_back(v);
        g[v].push_back(u);
    }
    dfs(1, -1);
    if(root_child>1){
        articulation_point[1] = true;
    }else{
        articulation_point[1] = false;
    }
    cout<<accumulate(all(articulation_point),0ll)<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}