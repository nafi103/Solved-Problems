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

vector<vector<pair<int,int>>>g;

void add(int u, int v, int w){
    g[u].pb({v,w});
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int n,m,k;
    cin>>n>>m>>k;
    g.resize(n+1);
    while(m--){
        int u,v,w;
        cin>>u>>v>>w;
        add(u,v,w);
    }
    vector<multiset<int,greater<int>>>distance(n+1);
    using pii = pair<int,int>;
    priority_queue<pii,vector<pii>,greater<pii>>pq;
    pq.push({0,1}); //first -> distance, second -> node
    while(!pq.empty()){
        auto [d,node] = pq.top();
        pq.pop();
        if(sz(distance[node])>=k and d>*distance[node].begin()) continue;
        for(auto &[child,dist]: g[node]){
            if(sz(distance[child])<k or dist+d<*distance[child].begin()){
                distance[child].insert(dist+d);
                if(sz(distance[child])>k) distance[child].erase(distance[child].begin());
                if(dist+d<=*distance[child].begin()) pq.push({dist+d,child});
            }
        }
    }
    for(auto it = distance[n].rbegin(); it!=distance[n].rend(); it++){
        cout<<*it<<" ";
    }
    cout<<endl;
}