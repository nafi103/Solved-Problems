#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int unsigned long long
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

/****************************************************************/
vector<vector<int>> multiply(vector<vector<int>>&a, vector<vector<int>>&b){
    int n = sz(a), m = sz(a[0]);
    vector<vector<int>>result(n,vector<int>(m,0));
    for(int i = 0; i<n; i++){
        for(int j = 0; j<m; j++){
            for(int k = 0; k<m; k++){
                result[i][j]+=(a[i][k]*b[k][j]);
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
    int p,q,n;
    cin>>p>>q>>n;
    int f = p*p - 2*q;
    vector<vector<int>>t(2,vector<int>(2,0));
    t[0][0] = p; t[1][0] = -q; t[0][1] = 1;
    if(n==0){
        cout<<2<<endl;
        return;
    }
    if(n==1){
        cout<<p<<endl;
        return;
    }
    t = expo(t,n-2);
    vector<vector<int>> ans = {{f,p}};
    ans = multiply(ans,t);
    cout<<ans[0][0]<<endl;
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