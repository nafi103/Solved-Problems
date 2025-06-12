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
int expo(int a, int b, int m)
{
    a%=m;
    int res = 1;
    while (b > 0)
    {
        if (b & 1)
            res = (res * a) % m;
        a = (a * a) % m;
        b = b >> 1;
    }
    return res;
}

int mminvprime(int a, int b) { return expo(a, b - 2, b); }

const int N = sqrt(INT_MAX) + 10;
vector<int>primes;

void solve()
{
    int n,m;
    cin>>n>>m;
    vector<pair<int,int>>prime_fact;
    for(auto &x: primes){
        if(x*x>n)
            break;
        if(n%x==0){
            int cnt = 0;
            while(n%x==0){
                n/=x;
                cnt++;
            }
            prime_fact.push_back({x,cnt*m});
        }
    }
    if(n>1){
        prime_fact.push_back({n,m});
    }
    int ans = 1;
    for(auto &[p,e]: prime_fact){
        int curr = ((expo(p,e+1,mod) - 1 + mod)%mod * mminvprime(p-1,mod))%mod;
        ans = (ans*curr)%mod;
    }
    cout<<ans<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    vector<bool>mark(N,true);
    for(int i = 2; i<N; i++){
        if(mark[i]){
            primes.push_back(i);
            for(int j = i*i; j<N; j+=i){
                mark[j] = false;
            }
        }
    }
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}