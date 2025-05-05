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
using vi = vector<int>;
vector<bool>articulation_point;

void dfs(int node, vector<vi>&g, vi &dfs_num, vi &dfs_low, int &cnt, int parent){
    dfs_num[node] = ++cnt;
    dfs_low[node] = dfs_num[node];
    int children = 0;
    for(auto &x: g[node]){
        if(dfs_num[x]==-1){
            children++;
            dfs(x,g,dfs_num,dfs_low,cnt,node);
            dfs_low[node] = min(dfs_low[node],dfs_low[x]);
            if(dfs_num[node]<=dfs_low[x] and node!=1) articulation_point[node] = true;
        }else if(x!=parent){
            dfs_low[node] = min(dfs_low[node], dfs_num[x]);
        }
    }
    if(node==1 and children>1) articulation_point[1] = true;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int n;
    while(cin>>n and n){
        articulation_point.clear();
        articulation_point.assign(n+1,false);
        cin.ignore();
        vector<vi>g(n+1);
        string str;
        while(getline(cin,str) and str[0]!='0'){
            stringstream s(str);
            s>>str;
            int u = stoi(str);
            while(s>>str){
                int v = stoi(str);
                g[u].pb(v);
                g[v].pb(u);
            }
        }
        vi dfs_num(n+1,-1), dfs_low(n+1);
        int cnt = 0,ans = 0;
        dfs(1,g,dfs_num,dfs_low,cnt,-1);
        for(int i = 1; i<=n; i++){
            if(articulation_point[i]) ans++;
        }
        debug(articulation_point)
        cout<<ans<<endl;
    }
}