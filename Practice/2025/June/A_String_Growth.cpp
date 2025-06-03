#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 1e9+7;
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
vector<vector<int>> multiply(vector<vector<int>>&a, vector<vector<int>>&b){
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
    int n,x,m,y,k;
    cin>>n>>x>>m>>y>>k;
    if(n>=44 or m>=44){
        cout<<"Impossible"<<endl;
        return;
    }
    if(n<m){
        swap(n,m);
        swap(x,y);
    }
    vector<vector<int>>t1(2,vector<int>(2,1)),t2(2,vector<int>(2,1)),t3(2,vector<int>(2,1));
    t1[1][1] = t2[1][1] = t3[1][1] = 0;
    t1 = expo(t1,n);
    t2 = expo(t2,m);
    int l = lcm(t1[1][0],t2[1][0]);
    int m1 = l/t1[1][0], m2 = l/t2[1][0];
    int nom = x*m1 - y*m2, denom = t1[0][0]*m1 - t2[0][0]*m2;
    if(nom%denom!=0){
        cout<<"Impossible"<<endl;
        return;
    }
    int b = nom/denom;
    nom = x-t1[0][0]*b; denom = t1[1][0];
    if(nom%denom!=0){
        cout<<"Impossible"<<endl;
        return;
    }
    int a = nom/denom;
    if(a<0 or b<0){
        cout<<"Impossible"<<endl;
        return;
    }
    vector<vector<int>>ini = {{b,a}};
    t3 = expo(t3,k);
    cout<<multiply(ini,t3)[0][0]<<endl;
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
        cout<<"Case "<<z<<": ";
        solve();
    }
}