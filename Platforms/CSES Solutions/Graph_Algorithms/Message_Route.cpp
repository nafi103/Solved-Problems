#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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


int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int n,m;
    cin>>n>>m;
    g.resize(n+1);
    for(int i = 1; i<=m; i++){
        int u,v;
        cin>>u>>v;
        g[u].pb(v);
        g[v].pb(u);
    }
    vector<int>parent(n+1,-1);
    queue<int>q;
    q.push(1);
    while(!q.empty()){
        int node = q.front();
        q.pop();
        for(auto &x: g[node]){
            if(x!=1 and parent[x]==-1){
                parent[x] = node;
                q.push(x);
            }
        }
    }
    deque<int>d;
    int curr = n;
    while(curr!=-1){
        d.push_front(curr);
        curr = parent[curr];
    }
    if(d.front()!=1){
        cout<<"IMPOSSIBLE"<<endl;
    }else{
        cout<<sz(d)<<endl;
        for(auto &x: d) cout<<x<<" ";
        cout<<endl;
    }
}