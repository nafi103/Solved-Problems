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

void dfs(int node, int par, vector<int>&parent, vector<set<int>>&t){
    parent[node] = par;
    for(auto &child: t[node]){
        if(child!=par){
            dfs(child,node,parent, t);
        }
    }
}


void solve()
{
    int n;
    cin>>n;
    vector<set<int>>t(n+1);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].insert(v);
        t[v].insert(u);
    }
    int cut = n-1,ans = n-1,curr_level = 0;
    vector<int>parent(n+1,-1);
    dfs(1,-1,parent,t);
    using arr = array<int,3>;
    set<arr>pq;
    pq.insert({1,0,1});
    while(!pq.empty()){
        curr_level++;
        while(!pq.empty() and (*pq.begin())[0] == 0 and (*pq.begin())[1]<curr_level){
            cut++;
            auto [leaf,level,node] = *pq.begin();
            pq.erase(pq.begin());
            t[parent[node]].erase(node);
            if(sz(t[parent[node]])==1 and parent[node]!=1) 
                pq.insert({0,level-1,parent[node]});
        }
        vector<pair<int,int>>add;
        while(!pq.empty()){
            auto [leaf,level,node] = *pq.begin();
            pq.erase(pq.begin());
            for(auto &child: t[node]){
                if(child!=parent[node]){
                    cut--;
                    if(sz(t[child])==1)
                        add.push_back({0,child});
                    else
                        add.push_back({1,child});
                }
            }
        }
        for(auto &[leaf,node]: add){
            pq.insert({leaf,curr_level,node});
        }
        ans = min(ans, cut);
    }
    cout<<ans<<endl;
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