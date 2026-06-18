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
int mod_add(int a, int b) {a = a % mod; b = b % mod; return (((a + b) % mod) + mod) % mod;}
int mod_mul(int a, int b) {a = a % mod; b = b % mod; return (((a * b) % mod) + mod) % mod;}
int mod_sub(int a, int b) {a = a % mod; b = b % mod; return (((a - b) % mod) + mod) % mod;}

int rev(int n, int p ){
    vector<int>temp;
    while(n){
        temp.pb(n%p);
        n/=p;
    }
    reverse(all(temp));
    int ans = 0, b = 1;
    for(int &x: temp){
        ans+=x*b;
        b*=p;
    }
    return ans;
}

int sum(int l, int r){
    return (r*(r+1)/2) - (l*(l-1)/2);
}

int sqsum(int l, int r){
    l--;
    return (r*(r+1)*(2*r+1))/6 - (l*(l+1)*(2*l+1))/6;
}


void solve()
{
    int n,p,ans = 0;
    cin>>n>>p;
    int l = 2;
    while(l*l<=n and l<=p){
        ans+=rev(n,l);
        l++;
    }
    for(int r = l; l<=p and l<=n; l = r+1){
        int q = n/l;
        r = min(p,n/(n/l));
        ans = mod_add(ans,n*sum(l,r));
        ans = mod_add(ans,(r-l+1)*q);
        ans = mod_sub(ans,q*sqsum(l,r));
    }
    if(p>n){
        ans = mod_add(ans,((p-n)%mod)*n);
    }
    cout<<ans%mod<<endl;
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