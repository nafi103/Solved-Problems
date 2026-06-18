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
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
const int N = 4e5+5;
vector<bool>prime(N,true);
using vi = vector<int>;
vector<vi>t;
vector<int>value,subtree_size, heavy_child;

int dfs(int node, int par){
    int max_weight = 0;
    for(auto &child: t[node]){
        if(child!=par){
            dfs(child,node);
            subtree_size[node]+=subtree_size[child];
            if(subtree_size[child]>max_weight){
                max_weight = subtree_size[child];
                heavy_child[node] = child;
            }
        }
    }
    return subtree_size[node];
}

void dfs_complete(int node, int par,int &val){
    if(par==-1){
        value[node] = val++;
    }else{
        while(val<N and prime[val-value[par]]) val++;
        value[node] = val++;
    }
    if(heavy_child[node]!=-1){
        dfs_complete(heavy_child[node],node,val);
    }
    for(auto &child: t[node]){
        if(child!=par and child!=heavy_child[node]) dfs_complete(child, node,val);
    }
}

void initialize(int n){
    t.resize(n+1);
    subtree_size.resize(n+1,1);
    heavy_child.assign(n+1,-1);
    value.resize(n+1);
}

void clearAll(){
    t.clear();
    subtree_size.clear();
    heavy_child.clear();
    value.clear();
}

void solve()
{
    int n;
    cin>>n;
    initialize(n);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].pb(v);
        t[v].pb(u);
    }
    int start = 1;
    for(int i = 1; i<=n; i++){
        if(sz(t[i])==1){
            start =  i;
            break;
        }
    }
    dfs(start,-1);
    int curr_val = 1;
    dfs_complete(start,-1,curr_val);
    if(curr_val>2*n+1){
        cout<<-1<<endl;
        return;
    }
    for(int i = 1; i<=n; i++) cout<<value[i]<<" ";
    cout<<endl;
    clearAll();
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    prime[1] = false;
    for(int i = 2; i*i<N; i++){
        if(prime[i]){
            for(int j = i*i; j<N; j+=i) prime[j] = false;
        }
    }
    int t = 1;
    cin>>t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}