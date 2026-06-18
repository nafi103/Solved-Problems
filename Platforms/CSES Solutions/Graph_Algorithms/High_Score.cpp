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
    vector<array<int,3>>edges;
    int n;
    Graph(int _n){
        n = _n;
    }
    void add(int u, int v, int w){
        edges.pb({u,v,w});
    }
    int bellman(){
        vector<bool>in_path(n+1,false),from_src(n+1,false);
        in_path[n] = true;
        from_src[1] = true;
        vector<int>ans(n+1,-inf);
        ans[1] = 0;
        for(int i = 1; i<=n; i++){
            for(auto &[u,v,w]: edges){
                from_src[v] = from_src[u]|from_src[v];
                in_path[u] = in_path[u]|in_path[v];
                if(ans[u]+w>ans[v]){
                    if(i==n and in_path[v] and from_src[v]) return -1;
                    ans[v] = ans[u]+w;
                }
            }
        }
        
        return ans[n];
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
    cout<<g.bellman()<<endl;
}