#include <iostream>
#include <vector>
#include <algorithm>

using namespace std;

struct WeaponClass {
    int profit;  // Difference between ingots used and returned (a_i - b_i)
    int ingot_type; // Type of metal needed for crafting
};

bool compareProfits(const WeaponClass& a, const WeaponClass& b) {
    return a.profit > b.profit; // Sort by descending profit
}

int main() {
    int n, m;
    cin >> n >> m;

    vector<WeaponClass> classes(n);
    for (int i = 0; i < n; ++i) {
        int a, b;
        cin >> a >> b;
        classes[i] = {a - b, i}; // Efficiently store profit and ingot type
    }

    vector<int> c(m);
    for (int i = 0; i < m; ++i) {
        cin >> c[i];
    }

    sort(classes.begin(), classes.end(), compareProfits); // Sort by profit

    int total_exp = 0;
    for (const WeaponClass& cls : classes) {
        if (cls.profit <= 0) continue; // Skip non-profitable classes

        int ingots_used = min(2 * c[cls.ingot_type], cls.profit); // Max ingots or cycles
        total_exp += ingots_used / cls.profit * 2; // Calculate total experience
        c[cls.ingot_type] = max(c[cls.ingot_type] - ingots_used / 2, 0); // Update remaining ingots
    }

    cout << total_exp << endl;

    return 0;
}
