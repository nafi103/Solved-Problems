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
int n,dfs_cnt = 0;
vector<pair<int,int>>ans;
vector<int>dfs_num,dfs_low;
vector<bool>visited;
vector<vector<int>>g;

void dfs(int node, int parent){
    visited[node] = true;
    dfs_num[node] = dfs_low[node] = dfs_cnt++;
    for(auto &nbr: g[node]){
        if(!visited[nbr]){
            dfs(nbr,node);
            dfs_low[node] = min(dfs_low[node],dfs_low[nbr]);
            if(dfs_num[node]<dfs_low[nbr]){
                ans.push_back({node,nbr});
            }
        }else if(nbr!=parent){
            dfs_low[node] = min(dfs_low[node],dfs_num[nbr]);
        }
    }
}


void solve()
{
    ans.clear();
    dfs_cnt = 0;
    g.clear();
    dfs_num.clear();
    dfs_low.clear();
    visited.clear();
    cin>>n;
    g.resize(n);
    dfs_low.resize(n);
    dfs_num.resize(n);
    visited.assign(n,false);
    for(int i = 0; i<n;  i++){
        int u,m;
        cin>>u;
        char x;
        cin>>x>>m>>x;
        while(m--){
            int v;
            cin>>v;
            g[u].push_back(v);
        }
    }
    for(int i = 0; i<n; i++){
        if(!visited[i]){
            dfs(i,-1);
        }
    }
    for(auto &[f,s]: ans){
        if(f>s)
            swap(f,s);
    }
    sort(all(ans));
    cout<<sz(ans)<<" critical links"<<endl;
    for(auto &[f,s]: ans){
        cout<<f<<" - "<<s<<endl;
    }
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
        cout<<"Case "<<z<<":\n";
        solve();
    }
}