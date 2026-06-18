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

struct Graph{
    int n;
    vector<vector<pair<int,int>>>g;
    Graph(int N){
        n = N;
        g.resize(n+1);
    }
    void add(int u, int v, int w){
        g[u].pb({v,w});
    }
    vector<int> dijstra(int src){
        vector<int> distance(n+1, inf);
        priority_queue <pair<int,int>, vector<pair<int,int>>, greater<pair<int,int>> > q; 
        distance[src] = 0;
        q.push({0,src});
        while(!q.empty()){
            auto [d,node] = q.top();
            q.pop();
            if(d>distance[node]) continue;
            for(auto &[child,dc]: g[node]){
                if(distance[child]>d+dc){
                    distance[child] = d+dc;
                    q.push({distance[child],child});
                }
            }
        }
        return distance;
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
    vector<int>distance = g.dijstra(1);
    for(int i = 1; i<=n; i++) cout<<distance[i]<<" ";
    cout<<endl;
}