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

struct Graph
{
    vector<int>parent;
    vector<array<int,3>>edges;
    int n;
    Graph(int _n){
        n = _n;
        parent.resize(n+1, -1);
    }
    void add(int u, int v, int w){
        edges.pb({u,v,w});
    }
    pair<bool,vector<int>> bellman(){
        int src,dst;
        vector<int>ans(n+1,inf);
        ans[1] = 0;
        for(int i = 1; i<=n; i++){
            for(auto &[u,v,w]: edges){
                if(ans[v]>ans[u]+w){
                    ans[v] = ans[u]+w;
                    parent[v] = u;
                }
            }
        }
        for(auto &[u,v,w]: edges){
            if(ans[v]>ans[u]+w){
                src = u;
                dst = u;
                vector<int>cycle_path;
                cycle_path.pb(src);
                src = parent[src];
                for(int i = 0; i<n and src!= dst; i++){
                    if(src==-1) break;
                    cycle_path.pb(src);
                    src = parent[src];
                }
                if(src==dst){
                    cycle_path.pb(src);
                    reverse(all(cycle_path));
                    return {true,cycle_path};
                }
            }
        }
        return {false,{}};
    }
};



int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int n,m;
    cin>>n>>m;
    Graph g(n);
    while(m--){
        int u,v,w;
        cin>>u>>v>>w;
        g.add(u,v,w);
    }
    auto [check,ans] = g.bellman();
    if(check){
        cout<<"YES"<<endl;
        writev(ans);
    }else{
        cout<<"NO"<<endl;
    }
}