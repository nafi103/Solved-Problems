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

bool check(vector<vi>&v, int &n, int  &m){
    for(int i = 0; i<n; i++){
        int cnt = 0;
        for(int j = 0; j<m; j++){
            if(v[i][j]!=j+1) cnt++;
        }
        if(cnt>2) return false;
    }
    return true;
}

void solve()
{
    int n,m;
    cin>>n>>m;
    vector<vi>v(n,vector<int>(m));
    for(auto &x: v) readv(x);
    for(int i = 0; i<m; i++){
        for(int j = 0; j<m; j++){
            for(int k = 0; k<n; k++) swap(v[k][i],v[k][j]);
            if(check(v,n,m)){
                puts("YES");
                return;
            }
            for(int k = 0; k<n; k++) swap(v[k][i],v[k][j]);
        }
    }
    puts("NO");
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