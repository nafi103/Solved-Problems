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

void dfs(vector<vector<int>>&t, int node, vector<bool>&visited){
    visited[node] = true;
    for(auto &x: t[node]){
        if(!visited[x]) dfs(t,x,visited);
    }
}

void change(vector<vector<int>>&t, int n, int rmv){
    vector<vector<int>>t2(n+1);
    for(int i = 1; i<=n; i++){
        if(i==rmv) continue;
        for(auto &x: t[i]){
            if(x==rmv) continue;
            t2[i].pb(x);
        }
    }
    t = t2;
}

int find_cc(vector<vector<int>>t, int rmv,int n){
    change(t,n,rmv);
    int mxEl = -1, ers = -1;
    for(int i = 1; i<=n; i++){
        if(i==rmv) continue;
        if(sz(t[i])>ers){
            ers = sz(t[i]);
            mxEl = i;
        }
    }
    change(t,n,mxEl);
    vector<bool>visited(n+1,false);
    int cc = 0;
    for(int i = 1; i<=n; i++){
        if(!visited[i] and i!=rmv and i!=mxEl){
            cc++;
            dfs(t,i,visited);
        }
    }
    return cc;
}

void solve()
{
    int n;
    cin>>n;
    vector<vector<int>>t(n+1);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].pb(v);
        t[v].pb(u);
    }
    if(n==2){
        cout<<0<<endl;
        return;
    }
    vector<pair<int,int>>adj;
    for(int i = 1; i<=n; i++){
        adj.pb({sz(t[i]),i});
    }
    sort(adj.rbegin(),adj.rend());
    cout<<max(find_cc(t,adj[0].ss,n), find_cc(t,adj[1].ss,n))<<endl;
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
        // google(z);
        solve();
    }
}