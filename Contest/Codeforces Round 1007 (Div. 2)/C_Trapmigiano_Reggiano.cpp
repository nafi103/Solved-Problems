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
vector<int>parent;
vector<vector<int>>t;

void dfs(int node, int par){
    parent[node] = par;
    for(auto &x: t[node]){
        if(x!=par){
            dfs(x,node);
        }
    }
}


void solve()
{
    t.clear();
    parent.clear();
    int n,st,en;
    cin>>n>>st>>en;
    t.resize(n+1);
    parent.resize(n+1);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].pb(v);
        t[v].pb(u);
    }
    if(n==1){
        cout<<1<<endl;
        return;
    }
    dfs(st,-1);
    int curr = en;
    vector<int>line;
    while(true){
        line.pb(curr);
        curr = parent[curr];
        if(curr==-1) break;
    }
    vector<int>level(n+1,-1);
    queue<pair<int,int>>q; //{node,level}
    vector<bool>visited(n+1,false);
    for(auto &x: line){
        level[x] = 0;
        visited[x] = true;
        q.push({x,0});
    }
    reverse(all(line));
    while(!q.empty()){
        auto [node,l] = q.front();
        q.pop();
        for(auto &child:t[node]){
            if(!visited[child]){
                level[child] = l+1;
                visited[child] = true;
                q.push({child,l+1});
            }
        }
    }
    vector<pair<int,int>>p;
    p.reserve(n+1);
    for(int i = 1; i<=n; i++){
        if(level[i]){
            p.push_back({level[i],i});
        }
    }
    sort(p.rbegin(),p.rend());
    for(auto &[l,node]: p){
        cout<<node<<" ";
    }
    for(auto &x: line){
        cout<<x<<" ";
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
        // google(z);
        solve();
    }
}