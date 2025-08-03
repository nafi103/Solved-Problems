#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 10;
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

vector<vector<int>> add(vector<vector<int>>a, vector<vector<int>>b){
    int n = sz(a);
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            a[i][j]+=b[i][j];
            a[i][j]%=mod;
        }
    }
    return a;
}

vector<vector<int>> add_identity(vector<vector<int>>a){
    for(int i = 0; i<sz(a); i++){
        a[i][i]++;
        a[i][i]%=mod;
    }
    return a;
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

vector<vector<int>>f(vector<vector<int>>mat, int k, vector<vector<int>>&ini){
    if(k==0) return vector<vector<int>>(sz(ini),vector<int>(sz(ini),0));
    if(k&1)
        return add(expo(ini,k),f(mat,k-1,ini));
    vector<vector<int>> f_of_halfk = f(mat,k>>1,ini);
    vector<vector<int>> mat_pow_halfk_plus_identity = add_identity(expo(ini,k>>1));
    return multiply(f_of_halfk,mat_pow_halfk_plus_identity);
}

void solve()
{
    int n,k;
    cin>>n>>k;
    vector<vector<int>>mat(n,vector<int>(n));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            cin>>mat[i][j];
        }
    }
    vector<vector<int>>ans = f(mat,k,mat);
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            cout<<ans[i][j];
        }
        cout<<endl;
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