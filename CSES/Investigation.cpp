#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 1000000007
#define inf 1e15+10
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


void solve()
{
    int n,m;
    cin>>n>>m;
    using pii = pair<int,int>;
    vector<vector<pii>>g(n+1);
    while(m--){
        int u,v,w;
        cin>>u>>v>>w;
        g[u].pb({v,w});
    }
    vector<int>mn(n+1,INT_MAX),mx(n+1,INT_MIN),ways(n+1,0),cost(n+1,inf);
    priority_queue<pii,vector<pii>,greater<pii>>pq;
    pq.push({0,1}); //first -> distance, second -> node
    mn[1] = 0; mx[1] = 0; cost[1] = 0,ways[1] = 1;
    while(!pq.empty()){
        auto [d,node] = pq.top();
        pq.pop();
        if(d>cost[node]) continue;
        for(auto &[child,w]: g[node]){
            if(d+w<cost[child]){
                cost[child] = d+w;
                mn[child] = mn[node]+1;
                mx[child] = mx[node]+1;
                ways[child] = ways[node];
                pq.push({cost[child],child});
            }else if(d+w==cost[child]){
                mn[child] = min(mn[child],mn[node]+1);
                mx[child] = max(mx[child],mx[node]+1);
                ways[child] = (ways[node]+ways[child])%mod;
            }
        }
    }
    printf("%lld %lld %lld %lld", cost[n],ways[n],mn[n],mx[n]);
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}