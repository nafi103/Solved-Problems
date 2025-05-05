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


void solve()
{
    int n,m;
    cin>>n>>m;
    vector<int>a(n),b(m);
    readv(a);
    readv(b);
    int mnpos = min_element(all(b)) - b.begin();
    int j = 0;
    reverse(b.begin(),b.begin()+mnpos);
    reverse(b.begin()+mnpos,b.end());
    reverse(all(b));
    for(int i = 0; i<n-m+1; i++){
        if(j==m) j = 0;
        if(j){
            a[i] = b[j];
            j++;
        }
        if(a[i]>b[0]){
            a[i] = b[0];
            j = 1;
        }
    }
    if(j){
        for(int i = n-m+1; j<m; i++,j++){
            a[i] = b[j];
        }
    }
    if(a[n-m]>=b[0]){
        bool flag = false;
        for(int i = n-m, j = 0; i<n; i++,j++){
            if(a[i]==b[j]) continue;
            if(a[i]<b[j]) break;
            else{
                flag = true;
                break;
            }
        }
        if(flag){
            for(int i = n-m, j = 0; i<n; i++,j++){
                a[i] = b[j];
            }
        }
    }
    writev(a);
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