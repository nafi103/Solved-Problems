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
int k, ans = 0;

struct Node{
    vector<int>adj, distance;
    Node(){
        distance.assign(k+1,0);
        distance[0] = 1;
    }
    void merge(Node & other){
        for(int i = 1; i<=k; i++)
            distance[i]+=other.distance[i-1];
    }

    void reroot(Node parent){
        for(int i = 1; i<=k; i++){
            parent.distance[i] -= distance[i-1];
        }
        for(int i = 1; i<=k; i++)
            distance[i]+=parent.distance[i-1];
    }
};

vector<Node>t;

void dfs(int node, int parent){
    for(auto &child: t[node].adj){
        if(child!=parent){
            dfs(child,node);
            t[node].merge(t[child]);
        }
    }
}

void find_pair(int node, int parent){
    if(parent!=-1){
        t[node].reroot(t[parent]);
    }
    ans+=t[node].distance[k];
    for(auto &child: t[node].adj){
        if(child!=parent){
            find_pair(child,node);
        }
    }
}

void solve()
{
    int n;
    cin>>n>>k;
    t.assign(n+1,Node());
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].adj.push_back(v);
        t[v].adj.push_back(u);
    }
    dfs(1,-1);
    find_pair(1,-1);
    cout<<ans/2<<endl;
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