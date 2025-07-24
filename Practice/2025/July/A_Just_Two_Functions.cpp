#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
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
int mod;

vector<vector<int>> multiply(vector<vector<int>>a, vector<vector<int>>b){
    int n = sz(a), m = sz(a[0]);
    vector<vector<int>>result(n,vector<int>(m,0));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            for(int k = 0; k<m; k++){
                result[i][j]+=(a[i][k]*b[k][j])%mod;
                result[i][j]%=mod;
            }
        }
    }
    return result;
}


vector<vector<int>> expo(vector<vector<int>>t, int p){
    int n = sz(t);
    vector<vector<int>>result(n,vector<int>(n,0));
    for(int i = 0; i<n; i++)
        result[i][i] = 1;
    while(p>0){
        if(p&1)
            result = multiply(result,t);
        t = multiply(t,t);
        p>>=1;
    }
    return result;
}

void solve()
{
    int a1,b1,c1,a2,b2,c2;
    cin>>a1>>b1>>c1>>a2>>b2>>c2;
    vector<int> f(3),g(3);
    readv(f);
    readv(g);
    cin>>mod;
    for(auto &x: f)
        x%=mod;
    for(auto &x: g)
        x%=mod;
    a1%=mod; b1%=mod; c1%=mod;
    a2%=mod; b2%=mod; c2%=mod;
    int q;
    cin>>q;
    vector<vector<int>>t(6,vector<int>(6,0)), ini(6,vector<int>(1));
    t[0][0] = a1;t[0][1] = b1;t[0][5] = c1;
    t[3][2] = c2;t[3][3] = a2;t[3][4] = b2;
    t[1][0] = t[2][1] = t[4][3] = t[5][4] = 1;
    for(int i = 0; i<3; i++)
        ini[i][0] = f[2-i];
    for(int i = 0; i<3; i++)
        ini[i+3][0] = g[2-i];
    debug(t)
    while(q--){
        int p;
        cin>>p;
        if(p<3){
            cout<<f[p]<<" "<<g[p]<<endl;
        }else{
            vector<vector<int>>ans = multiply(expo(t,p-2) , ini);
            cout<<ans[0][0]<<" "<<ans[3][0]<<endl;
        }
    }
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
        cout<<"Case "<<z<<":\n";
        solve();
    }
}