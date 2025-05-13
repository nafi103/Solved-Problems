#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 10007;
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
    int n,a,b,c;
    cin>>n>>a>>b>>c;
    if(n<=2){
        cout<<0<<endl;
        return;
    }
    n-=2;
    vector<vector<int>>t(4,vector<int>(4,0));
    t[0][0] = a;
    t[2][0] = b;
    t[3][0] = t[0][1] = t[1][2] = t[3][3] = 1;
    t = expo(t,n-1);
    vector<vector<int>> final(1,vector<int>(4,0));
    final[0][0] = final[0][3] = c;
    final = multiply(final,t);
    cout<<final[0][0]<<endl;
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