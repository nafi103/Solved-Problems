#include <bits/stdc++.h>
#define int long long
using namespace std;
 signed main() {
 int n, k; 
    cin >> n >> k;
     k -= 1; // make 0-based
        vector<int> divisors;
    for (int i = 1; i * i * 1ll <= n; i++) {
        if (n % i) continue;
        divisors.push_back(i);
         if (i * i == n) continue; // make duplicate, so take only once
        divisors.push_back(n / i);
    } 
    sort(divisors.begin(), divisors.end());
        int ans = -1;
    if (k < divisors.size()) { // k is less than total number of divisors
        ans = divisors[k];
    }
    cout << ans << endl;
    return 0;
}