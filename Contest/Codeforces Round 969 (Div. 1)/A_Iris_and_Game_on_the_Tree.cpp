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
vector<vector<int>>t;
string color;
vector<int>leaf;
int leaf_count;

void dfs(int node, int parent){
    if(node!=0 and sz(t[node])==1){
        leaf_count++;
        if(color[node]=='0')
            leaf[0]++;
        else if(color[node]=='1')
            leaf[1]++;
    }else if(node!=0 and color[node]=='?')
        leaf[2]++;
    for(auto &child: t[node]){
        if(child!=parent){
            dfs(child,node);
        }
    }
}


void solve()
{
    leaf_count = 0;
    leaf = {0,0,0};
    int n;
    cin>>n;
    t.resize(n);
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        u--,v--;
        t[u].pb(v);
        t[v].pb(u);
    }
    cin>>color;
    dfs(0,-1);
    if(color[0]!='?'){
        int root_color = color[0] - '0';
        int not_colored = leaf_count-leaf[0]-leaf[1];
        int max_get = (not_colored+1)/2;
        cout<<leaf[root_color^1] + max_get <<endl;
    }else{
        int add = 0, root_color = 0;
        if(leaf[0]==leaf[1]){
            if(leaf[2]&1)
                add = 1;
            root_color = 0;
        }else if(leaf[0]<leaf[1]){
            root_color = 0;
        }else{
            root_color = 1;
        }
        int not_colored = leaf_count-leaf[0]-leaf[1];
        int max_get = (not_colored+add)/2;
        cout<<leaf[root_color^1] + max_get <<endl;
    }
    t.clear();
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