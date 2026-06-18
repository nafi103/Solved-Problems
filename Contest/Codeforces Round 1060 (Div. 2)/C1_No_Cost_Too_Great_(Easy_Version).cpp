#include <bits/stdc++.h>
 using namespace std;
 /****************************************************************/
 #define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18 + 10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x) & (-x))
#define all(x) x.begin(), x.end()
#define endl "\n"
 #ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x)                                        \
    cerr << "Line " << __LINE__ << ": " << #x << " = "; \
    _print(x);                                          \
    cerr << endl;
#else
#define debug(...)
#endif
 /****************************************************************/
const int N = 2e5 + 10;
vector<int> spf(N);
 vector<int>get_prime(int x){
    vector<int> primes;
    while(x>1){
        int p = spf[x];
        primes.push_back(p);
        while(x%p==0){
            x /= p;
        }
    }
    return primes;
}
 bool one_possible(map<int,int>&prime_count, vector<int>&v){
    for(auto &x: v){
        vector<int> primes = get_prime(x);
        for(auto &p: primes)
            prime_count[p]--;
        primes = get_prime(x+1);
        for(auto &p: primes){
            if(prime_count[p]+1>1)
                return true;
        }
        primes = get_prime(x);
        for (auto &p : primes)
            prime_count[p]++;
    }
    return false;
}
 void solve()
{
    int n;
    cin >> n;
    vector<int> v(n),b(n);
    map<int, int> prime_count;
    for (auto &x : v)
    {
        cin >> x;
        vector<int> primes = get_prime(x);
        for(auto &p: primes)
            prime_count[p]++;
    }
    for(auto &x: b)
        cin >> x;
    if(prime_count.empty()){
        cout << 2 << endl;
        return;
    }
    for(auto &[f,s]: prime_count){
        if(s>1){
            cout << 0 << endl;
            return;
        }
    }
    if(one_possible(prime_count,v)){
        cout << 1 << endl;
    }else{
        cout << 2 << endl;
    }
}
 int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    iota(all(spf), 0);
    for (int i = 2; i * i < N; i++)
    {
        if(spf[i]==i){
            for (int j = i * i; j < N; j+=i){
                spf[j] = min(spf[j], i);
            }
        }
    }
    for (int z = 1; z <= t; z++)
    {
        // cout<<"Case "<<z<<": ";
        solve();
    }
}