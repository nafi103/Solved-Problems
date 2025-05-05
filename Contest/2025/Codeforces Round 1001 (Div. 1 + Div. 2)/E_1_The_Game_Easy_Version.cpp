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
vector<int>w,fmx,smx;
pair<int,int>ans;
int abs_mx;

void resizeAll(int n){
    abs_mx = INT_MIN;
    ans = {-1,0};
    t.resize(n+1);
    w.resize(n+1);
    fmx.resize(n+1);
    smx.resize(n+1);
}

void clearAll(){
    t.clear();
    w.clear();
    fmx.clear();
    smx.clear();
}

void dfs(int node, int par){
    int mx = w[node],nmx = INT_MIN;
    for(auto &x: t[node]){
        if(x!=par){
            dfs(x,node);
            if(fmx[x]>mx){
                nmx = mx;
                mx = fmx[x];
            }else if(fmx[x]>nmx){
                nmx = fmx[x];
            }
        }
    }
    fmx[node] = mx, smx[node] = nmx;
}

void find_ans(int node, int par){
    for(auto &x: t[node]){
        if(x==par){
            if((smx[par]==fmx[node] or w[par]>w[node] or fmx[par]>fmx[node]) and w[node]!=abs_mx){
                if(ans.ff<w[node]){
                    ans = {w[node],node};
                }
            }
            break;
        }
    }
    for(auto &x: t[node]){
        if(x!=par){
            find_ans(x,node);
        }
    }
}


void solve()
{
    int n;
    cin>>n;
    resizeAll(n);
    for(int i = 1; i<=n; i++){
        cin>>w[i];
        abs_mx = max(abs_mx,w[i]);
    }
    for(int i = 1; i<n; i++){
        int u,v;
        cin>>u>>v;
        t[u].pb(v);
        t[v].pb(u);
    }
    dfs(1,-1);
    find_ans(1,-1);
    cout<<ans.ss<<endl;
    clearAll();
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